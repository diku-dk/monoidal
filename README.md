# Composable Monoids in Futhark [![CI](https://github.com/diku-dk/monoidal/workflows/CI/badge.svg)](https://github.com/diku-dk/monoidal/actions) [![Documentation](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/status.svg)](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/latest/)

A library for composable monoids in Futhark. The library allows for processing
formatted byte sequences using a single monoidal operation. Examples include
finding the maximum average of grouped floats and computing a sum of products,
with nested parentheses of a predefined depth. The library is documented in the
tech report [Generic Combinators for Monoid Nesting in Futhark](https://elsman.com/pdf/monoids.pdf)
and is heavily inspired by Oleg Kiselyov's paper [More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
and the associated OCaml code.

For examples, consult the file [monoidal_ex.fut](lib/github.com/diku-dk/monoidal/monoidal_ex.fut).

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

## An Example Explained

Consider a large text file containing floats separated by commas
(`,`) and grouped by bars (`|`). An input text file may contain the string
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

## Simple JSON queries

The [monoidal_json.fut](lib/github.com/diku-dk/monoidal/monoidal_json.fut)
library builds on the functionality of
[monoidal.fut](lib/github.com/diku-dk/monoidal/monoidal.fut). Its JSON-specific
combinators describe supported fields, records, and arrays; the generic monoidal
combinators provide projection, filtering, and aggregation. Parsing and
aggregation are composed into a single reduction over the input bytes.

For example, the following query sums `score` for records whose `id` is 5:

```json
[{"id":5,"score":8.25},{"id":2,"score":2.0},{"id":5,"score":2.25}]
```

The result is `10.5`. The query in
[json_ex.fut](lib/github.com/diku-dk/monoidal/json_ex.fut) is constructed as follows:

```futhark
import "monoidal"
import "monoidal_json"
module M = monoidal
module J = monoidal_json

-- Convert the schema's nested tuple to a named record at observation.
type row = {id:u64,score:f64}
module Record = {
  local module Id = J.field {type t=u64} J.nat {
    def key = J.Key.pack "id"
    def default = 0u64
  }
  local module Score = J.field {type t=f64} J.number {
    def key = J.Key.pack "score"
    def default = 0f64
  }
  local module Fields = J.Record.Succ Id (J.Record.Succ Score J.Record.Zero)
  local module Parsed = J.Record.Make Fields
  open Parsed.with_obs {
    type o = row
    def obs ((id,(score,())):Fields.v) : o = {id,score}
  }
}
module ScoreSum = M.sum f64
module ProjectedScores = M.with_gen ScoreSum {
  type i = Record.v
  def gen (r:i) = r.score
}
module Scores = M.input_filter ProjectedScores {def pred (r:Record.v) = r.id == 5}
module Query = J.array_records Record Scores

def query (xs:[]u8) : opt f64 =
  Query.obs (reduce Query.op Query.ne (map Query.gen xs))
```

`Record.Zero` and `Record.Succ` assemble the field schema, `Record.Make`
constructs the parser, and its `with_obs` converts the tuple into a named record.
`input_filter` makes valid records with other IDs contribute the sum's neutral
element, zero. Invalid records still cause the query to fail. The query returns
`#some sum` on success and `#none` on malformed input; the example's `main` entry
point exposes this as `(true, sum)` or `(false, 0)`.

### Running the example

From the repository root, compile the supplied example with the sequential C
backend and create a small input file. Use `printf` to avoid a trailing newline,
since this restricted parser does not accept whitespace:

```sh
futhark c -o /tmp/json_ex lib/github.com/diku-dk/monoidal/json_ex.fut
printf '%s' '[{"id":5,"score":8.25},{"id":2,"score":2.0},{"id":5,"score":2.25}]' > /tmp/id-score.json
jq -Rs . < /tmp/id-score.json | futhark dataset --binary | /tmp/json_ex
```

This prints:

```text
true
10.5f64
```

Here `jq -Rs .` encodes the file contents as a string, and `futhark dataset`
converts that string to a binary `[]u8`. This only wraps the input bytes;
`json_ex` performs the JSON parsing and query evaluation.

For multicore execution, compile with `futhark multicore` and choose the number
of workers:

```sh
futhark multicore -o /tmp/json_ex_mc lib/github.com/diku-dk/monoidal/json_ex.fut
jq -Rs . < /tmp/id-score.json | futhark dataset --binary |
  /tmp/json_ex_mc --num-threads 4
```

### Supported fragment

Fields may appear in any order. Missing fields use their configured defaults;
duplicate fields take the last value. Unknown fields or malformed values cause
failure, and configured field keys must be distinct.

This is deliberately a restricted JSON fragment: quoted keys contain 1–7 ASCII
letters, digits, or underscores; whitespace, escapes, and nested field values
are unsupported. Records must be nonempty, but arrays may be empty. The `nat`
parser allows leading zeros and wraps on overflow; `number` accepts decimal
notation with at most 18 digits and no exponent. These parsers do not validate
the full JSON grammar.

## Test Usage

Run the examples and all regression tests:
```
$ make test
```

Regression sources and their shared helpers live in
`lib/github.com/diku-dk/monoidal/test/`. To typecheck the
suite or run it with the interpreter, use `make test TEST_FLAGS=-t` or
`make test TEST_FLAGS=-i`. Select the multicore backend with
`make test BACKEND=multicore`.

## License

MIT License - see the associated [LICENSE](LICENSE) file.

## References

[1] Martin Elsman. Generic Combinators for Monoid Nesting in Futhark - Towards a
library for data-parallel one-touch queries in constant space. DIKU Technical
Report. Department of Computer Science, University of
Copenhagen. September 2026. [pdf](https://elsman.com/pdf/monoids.pdf)

[2] Oleg Kiselyov. More Fun with Monoids. In Proceedings of the 2026 Symposium
on Functional and Logic Programming. FLOPS 2026. Lecture Notes in Computer
Science, vol 16533. Springer. 2026. [pdf](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
