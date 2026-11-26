import "../monoidal"
import "../monoidal_json"
module M = monoidal
module J = monoidal_json
module Id = J.field {type t=u64} J.nat {
  def key = J.Key.pack "id"
  def default = 7u64
}
module Score = J.field {type t=f64} J.number {
  def key = J.Key.pack "score"
  def default = 1.5f64
}
module Active = J.field {type t=bool} J.bool {
  def key = J.Key.pack "active"
  def default = true
}
module Extra = J.field {type t=u64} J.nat {
  def key = J.Key.pack "extra"
  def default = 99u64
}
module Schema = J.Record.Succ Id (J.Record.Succ Score (J.Record.Succ Active J.Record.Zero))
module R = J.Record.Make Schema
module One = J.Record.Make (J.Record.Succ Id J.Record.Zero)
module Zero = J.Record.Make J.Record.Zero
module Four = J.Record.Make (J.Record.Succ Extra Schema)
module Query = J.array_records R (M.count {type i=R.v})
module Run (P:monoid with i=u8) = {
  def run xs = P.obs (reduce P.op P.ne (map P.gen xs))
}
module RR = Run R
module RO = Run One
module RZ = Run Zero
module RF = Run Four
module RQ = Run Query
module Body = R.body

def flatten (x:opt R.v) = match x
  case #some (id,(score,(active,()))) -> (true,id,score,active)
  case #none -> (false,0u64,0f64,false)

-- All test entry points follow the reusable definitions.
entry main (xs:[]u8) = flatten (RR.run xs)
entry one (xs:[]u8) = match RO.run xs
  case #some (v,()) -> (true,v)
  case #none -> (false,0u64)
entry zero (xs:[]u8) = match RZ.run xs case #some _ -> true case _ -> false
entry four (xs:[]u8) = match RF.run xs
  case #some (extra,(id,(score,(active,())))) -> (extra,true,id,score,active)
  case #none -> (0u64,false,0u64,0f64,false)
entry array_count (xs:[]u8) = match RQ.run xs
  case #some n -> (true,n)
  case #none -> (false,0i64)
-- Check every three-way split, including empty fragments and neutral contexts.
entry laws (xs:[]u8) =
  let parts = map Body.gen xs
  let fold ys = reduce Body.op Body.ne ys
  let expected = Body.obs (fold parts)
  in reduce (&&) true (map (\i ->
    reduce (&&) true (map (\j ->
      let a = fold parts[:i]
      let b = fold parts[i:j]
      let c = fold parts[j:]
      let l = Body.op (Body.op a b) c
      let r = Body.op a (Body.op b c)
      in Body.obs l == expected && Body.obs r == expected &&
         Body.obs (Body.op Body.ne l) == expected &&
         Body.obs (Body.op r Body.ne) == expected)
      (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))

-- ==
-- entry: main
-- input { "{\"id\":5,\"score\":2.5,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"id\":5,\"active\":false,\"score\":2.5}" } output { true 5u64 2.5f64 false }
-- input { "{\"score\":2.5,\"id\":5,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"score\":2.5,\"active\":false,\"id\":5}" } output { true 5u64 2.5f64 false }
-- input { "{\"active\":false,\"id\":5,\"score\":2.5}" } output { true 5u64 2.5f64 false }
-- input { "{\"active\":false,\"score\":2.5,\"id\":5}" } output { true 5u64 2.5f64 false }
-- input { "{}" } output { false 0u64 0f64 false }
-- input { "{\"active\":false}" } output { true 7u64 1.5f64 false }
-- input { "{\"id\":1,\"score\":2.5,\"id\":5,\"active\":true,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"id\":-1,\"id\":5}" } output { false 0u64 0f64 false }
-- input { "{\"active\":bad,\"active\":true}" } output { false 0u64 0f64 false }
-- input { "{\"other\":1}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1,}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1,,\"score\":2}" } output { false 0u64 0f64 false }
-- input { "{\"id\":}" } output { false 0u64 0f64 false }
-- input { "{\"id\"::1}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1 \"score\":2}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1" } output { false 0u64 0f64 false }
-- input { "{\"id\":[1,2]}" } output { false 0u64 0f64 false }
-- input { "{\"score\":{\"id\":1}}" } output { false 0u64 0f64 false }

-- ==
-- entry: one
-- input { "{\"id\":12}" } output { true 12u64 }
-- input { "{\"score\":2}" } output { false 0u64 }
-- input { "{}" } output { false 0u64 }

-- ==
-- entry: zero
-- input { "{}" } output { false }
-- input { "{\"id\":1}" } output { false }
-- input { "" } output { false }

-- ==
-- entry: four
-- input { "{\"active\":false,\"extra\":42,\"score\":2.5,\"id\":5}" } output { 42u64 true 5u64 2.5f64 false }

-- ==
-- entry: array_count
-- input { "[]" } output { true 0i64 }
-- input { "[{\"active\":false},{\"score\":2.5,\"id\":5}]" } output { true 2i64 }
-- input { "[{\"id\":-1}]" } output { false 0i64 }

-- ==
-- entry: laws
-- input { "" } output { true }
-- input { "\"id\":1" } output { true }
-- input { "\"active\":false,\"id\":5" } output { true }
-- input { "\"id\":1,\"id\":2" } output { true }
-- input { "\"id\":x,\"id\":2" } output { true }
-- input { "\"x\":1" } output { true }
