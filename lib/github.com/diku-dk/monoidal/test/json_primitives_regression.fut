import "../monoidal"
import "../monoidal_json"
module M = monoidal
module J = monoidal_json

entry boolean (xs:[]u8) : (bool,bool) =
  match J.bool.obs (reduce J.bool.op J.bool.ne (map J.bool.gen xs))
  case #some v -> (true,v)
  case #none -> (false,false)
entry natural (xs:[]u8) : (bool,u64) =
  match J.nat.obs (reduce J.nat.op J.nat.ne (map J.nat.gen xs))
  case #some v -> (true,v)
  case #none -> (false,0)
entry number (xs:[]u8) : (bool,f64) =
  match J.number.obs (reduce J.number.op J.number.ne (map J.number.gen xs))
  case #some v -> (true,v)
  case #none -> (false,0)

module Active = J.field {type t=bool} J.bool {
  def key = J.Key.pack "active"
  def default = false
}
module N = J.field {type t=u64} J.nat {
  def key = J.Key.pack "n"
  def default = 0u64
}
module R = J.Record.Make (J.Record.Succ Active (J.Record.Succ N J.Record.Zero))
entry record (xs:[]u8) : (bool,bool,u64) =
  match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some (a,(n,())) -> (true,a,n)
  case #none -> (false,false,0)

entry boolean_splits (xs:[]u8) : bool =
  let parts = map J.bool.gen xs
  let fold ys = reduce J.bool.op J.bool.ne ys
  let expected = J.bool.obs (fold parts)
  in reduce (&&) true (map (\i ->
    reduce (&&) true (map (\j ->
      let a = fold parts[:i]
      let b = fold parts[i:j]
      let c = fold parts[j:]
      in J.bool.obs (J.bool.op (J.bool.op a b) c) == expected &&
         J.bool.obs (J.bool.op a (J.bool.op b c)) == expected)
      (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))

-- ==
-- entry: boolean
-- input { "true" } output { true true }
-- input { "false" } output { true false }
-- input { "True" } output { false false }
-- input { "FALSE" } output { false false }
-- input { "tru" } output { false false }
-- input { "falsex" } output { false false }
-- input { "truefalse" } output { false false }
-- input { "\"true\"" } output { false false }
-- input { " true" } output { false false }
-- input { "" } output { false false }

-- ==
-- entry: natural
-- input { "0" } output { true 0u64 }
-- input { "0005" } output { true 5u64 }
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { true 0u64 }
-- input { "-0" } output { false 0u64 }
-- input { "1.0" } output { false 0u64 }
-- input { "" } output { false 0u64 }

-- ==
-- entry: number
-- input { "-12.75" } output { true -12.75f64 }
-- input { "005.25" } output { true 5.25f64 }
-- input { "1e2" } output { false 0f64 }
-- input { ".5" } output { false 0f64 }
-- input { "5." } output { false 0f64 }
-- input { "0000000000000000000" } output { false 0f64 }
-- input { "" } output { false 0f64 }

-- ==
-- entry: record
-- input { "{\"active\":true,\"n\":12}" } output { true true 12u64 }
-- input { "{\"n\":2,\"active\":false}" } output { true false 2u64 }
-- input { "{\"n\":3}" } output { true false 3u64 }
-- input { "{\"active\":true,\"active\":false}" } output { true false 0u64 }
-- input { "{\"active\":TRUE}" } output { false false 0u64 }
-- input { "{\"active\":\"true\"}" } output { false false 0u64 }
-- input { "{\"active\":true,\"n\":bad}" } output { false false 0u64 }

-- ==
-- entry: boolean_splits
-- input { "true" } output { true }
-- input { "false" } output { true }
-- input { "truefalse" } output { true }
-- input { "" } output { true }
