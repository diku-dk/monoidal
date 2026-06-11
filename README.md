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

## Test Usage

To test the library, run the associated examples, as follows:
```
$ futhark test lib/github.com/diku-dk/monoidal/monoidal_ex.fut
```

## License

MIT License - see the associated [LICENSE](LICENSE) file.
