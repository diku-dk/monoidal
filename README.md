# Composable Monoids in Futhark [![CI](https://github.com/diku-dk/monoidal/workflows/CI/badge.svg)](https://github.com/diku-dk/monoidal/actions) [![Documentation](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/status.svg)](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/latest/)

A library for composable monoids in Futhark. The library allows for processing
formatted byte sequences using a single monoidal operation. Examples include
finding the maximum average of grouped floats. The library is heavily inspired by
Oleg Kiselyov's paper [More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
and the associated OCaml code.

This package also contains monoid-based functionality for majority voting
through a parameterised module
[`mk_majority`](lib/github.com/diku-dk/monoidal/majority.fut). This monoid-based
functionality is also described in details in Oleg Kiselyov's paper
[More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf).

## Tuple-backed parentheses

`monoidal.Parens.Zero`, `Succ` and `Make` construct homogeneous nesting with
inductive tuples and compact byte metadata (depths 0–49). Existing nesting
combinators remain available. See the [interface, example and proof status](lib/github.com/diku-dk/monoidal/Parens.md).

## Installation

```
$ futhark pkg add github.com/diku-dk/monoidal
$ futhark pkg sync
```

## Example

As an example, consider a large text file containing floats separated by commas
(`,`) and grouped by bars (`|`). An example text file may contain the string
`"12.1,45.3|10,93.2,2|23"`. Now consider the task of computing the maximum of the
averages of the groups of floats. Here is how we can construct a monoid for
carrying out the task:

```futhark
module max_avgs : { val red [n] : [n]u8 -> f64 } = {
  open monoidal

  module avg (X:numeric) : monoid with i = X.t with o = X.t = {
    open dup { type i = X.t }
	     (prod (sum X) (count { type i = X.t }))
    type o = X.t
    def obs (t:t) : o =
      let (s,c) = obs t
      in if c == 0 then X.i64 0 else s X./ (X.i64 c)
  }

  module groups = chunk (max f64) (optone f64) { def del_ign (c:u8) : bool = c == '|' }
  module items = chunk (avg f64) groups { def del_ign (c:u8) : bool = c == ',' }
  module M = chunk (float f64) items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : f64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}
```

We first define a monoid for computing the average of a series of values. This
monoid uses the `prod` monoid combinator for maintaining the sum and the count of
underlying values. It also uses the `with_obs` combinator for refining how
monoid values are observed (using float division). We then use the `chunk`
combinator for defining which monoid is used on values separated by commas and
which monoid is used on values that are observed by the grouping. The `chunk`
combinator is also used for parsing the individual floats and for passing the
floats to the higher-level monoid. Finally, we define an operation `red`, which
takes a sequence of characters and uses the defined monoid to process the
sequence.

```
$ futhark repl lib/github.com/diku-dk/monoidal/monoidal_ex.fut
[0]> max_avgs.red "12.1,45.3|10,93.2,2|23"
35.06666666666667
```

## Restricted decimal parsing

`monoidal.decimal f64` is an alternative to `float f64` for the grammar
`-?[0-9]+(\.[0-9]+)?`, with at most 18 digits in total, including leading
zeros. A leading minus is supported; a plus, exponent, whitespace, missing
integer part, or missing fractional part is not. `decimal_try f64` has the
same summary and returns `#none` for invalid complete inputs, whereas
`decimal f64` asserts when an invalid result is observed.

The summary contains an unsigned integer mantissa, digit count, fractional
digit count (or -1 for no point), and sign flag, plus failure/minus-only
constructors. Fragment combination accumulates digits exactly in `u64`;
an explicit case function supplies powers of ten. Conversion and decimal
scaling happen at observation, preserving negative zero for floating-point
outputs. This may round differently from `float`; no correctly-rounded
decimal-to-binary conversion guarantee is made. The summary laws apply to
the reachable, bounded representations, not arbitrary fabricated records.

`benchmarks/sumproducts/expr_decimal.fut` replaces only the numeric parser
in the `parens_hom` expression benchmark. `compare_decimal.py` compares it
with the `float` variant using the saved depth-one datasets. The new parser
has regression tests for fragment associativity and identities, but no
separate Rocq development yet.

## Integrated nested numeric parsers

`float_nested f64` and `decimal_nested f64` consume `nest u8 f64` directly,
without a separate `nestable` wrapper. Their `_try` variants observe failures
as `#none`; the ordinary variants assert on invalid observation. A nested
value is an entire operand: it may combine with the neutral element, but
not with any nonempty raw fragment or another nested value. Raw-number
grammars and rounding follow the corresponding ordinary parser. The raw
parsing operations are shared, not independently reimplemented.

Decimal uses one `u64` payload for either the mantissa or the exact bits of
the nested value. Its module parameter implements `numeric_bits64`:
`numeric` plus `to_bits : t -> u64` and `from_bits : u64 -> t`, required to
be lossless inverses. `f64` implements this interface; `f32` does not match
its 64-bit signatures directly. Float remains parameterised over `numeric`.
The decimal record merges the parser/nesting tags; float uses a single sum
type with an additional nested-value constructor.

The integrated parsers have regression tests against a total model of
generic nesting, including malformed adjacency, fragment splits, signed
zero, infinities, and NaN payload preservation. These are tests, not a new
Rocq proof. See `benchmarks/sumproducts/expr_decimal_nested.fut` and
`expr_float_nested.fut` for expressions using the new modules.

The first integrated-decimal experiment reduces the lowered partition payload
from 208 to 154 bytes, but is slower than `nestable (decimal f64)` in the
expression benchmark. It is not currently recommended as a speed optimisation;
the existing examples remain unchanged. Full measurements are in
`benchmarks/sumproducts/results-decimal-nested/REPORT.md`.

## Test Usage

To test the library, run the associated examples, as follows:
```
$ futhark test lib/github.com/diku-dk/monoidal/monoidal_ex.fut
```

## License

MIT License - see the associated [LICENSE](LICENSE) file.
