import "../monoidal"
import "../monoidal_json"
open monoidal
open monoidal_json

-- A different schema and aggregation exercise the reusable layer.
module A = monoidal_json.field {type t=u64} (nat_try u64) {
  def key = Key.pack "a"
  def default = 7u64
}
module B = monoidal_json.field {type t=f64} (decimal_try f64) {
  def key = Key.pack "b"
  def default = 1.5f64
}
module R = monoidal_json.Record.Make
  (monoidal_json.Record.Succ A
    (monoidal_json.Record.Succ B monoidal_json.Record.Zero))
module Query = monoidal_json.array_records R (count {type i=R.v})

module Named = R.with_obs {
  type o = {a:u64,b:f64}
  def obs ((a,(b,())):R.v) : o = {a,b}
}
def named_result (x:opt Named.v) = match x
  case #some r -> (true,r.a,r.b)
  case #none -> (false,0u64,0f64)

entry record (xs:[]u8) : (bool,u64,f64) =
  match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some (a,(b,())) -> (true,a,b)
  case #none -> (false,0,0)

entry array_count (xs:[]u8) : (bool,i64) =
  match Query.obs (reduce Query.op Query.ne (map Query.gen xs))
  case #some n -> (true,n)
  case #none -> (false,0)

entry named_record (xs:[]u8) =
  named_result (Named.obs (reduce Named.op Named.ne (map Named.gen xs)))

entry named_body (xs:[]u8) =
  named_result (Named.body.obs
    (reduce Named.body.op Named.body.ne (map Named.body.gen xs)))

-- ==
-- entry: named_record
-- input { "{\"b\":2.5,\"a\":12}" } output { true 12u64 2.5f64 }
-- input { "{\"a\":0}" } output { true 0u64 1.5f64 }
-- input { "{\"a\":bad}" } output { false 0u64 0f64 }
-- input { "{}" } output { false 0u64 0f64 }

-- ==
-- entry: named_body
-- input { "\"b\":2.5,\"a\":12" } output { true 12u64 2.5f64 }
-- input { "\"a\":0" } output { true 0u64 1.5f64 }
-- input { "\"a\":bad" } output { false 0u64 0f64 }
-- input { "" } output { false 0u64 0f64 }

-- ==
-- entry: record
-- input { "{\"a\":12,\"b\":3.25}" } output { true 12u64 3.25f64 }
-- input { "{\"b\":-2.5,\"a\":42}" } output { true 42u64 -2.5f64 }
-- input { "{\"a\":0}" } output { true 0u64 1.5f64 }
-- input { "{\"b\":0}" } output { true 7u64 0f64 }
-- input { "{\"a\":1,\"a\":2}" } output { true 2u64 1.5f64 }
-- input { "{}" } output { false 0u64 0f64 }
-- input { "{a:1}" } output { false 0u64 0f64 }
-- input { "{\"x\":1}" } output { false 0u64 0f64 }
-- input { "{\"a\":-1}" } output { false 0u64 0f64 }
-- input { "{\"a\":1,}" } output { false 0u64 0f64 }
-- input { "\"a\":1" } output { false 0u64 0f64 }
-- input { "{\"a\":1" } output { false 0u64 0f64 }
-- input { "{{\"a\":1}}" } output { false 0u64 0f64 }

-- ==
-- entry: array_count
-- input { "[]" } output { true 0i64 }
-- input { "[{\"a\":1,\"b\":2.5},{\"b\":0.25}]" } output { true 2i64 }
-- input { "[{\"a\":1}]" } output { true 1i64 }
-- input { "[{\"a\":1},{\"b\":bad}]" } output { false 0i64 }
-- input { "[{\"a\":1}{\"a\":2}]" } output { false 0i64 }
-- input { "[{\"a\":1},]" } output { false 0i64 }
-- input { "[{\"a\":1},,{\"a\":2}]" } output { false 0i64 }
-- input { "[{\"a\":1]" } output { false 0i64 }
-- input { "[[{\"a\":1}]]" } output { false 0i64 }
-- input { "[{\"a\":{\"a\":1}}]" } output { false 0i64 }
