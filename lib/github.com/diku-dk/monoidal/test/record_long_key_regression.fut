import "../monoidal"
import "../monoidal_json"
module J = monoidal_json
module Field = J.field {type t=u64} J.nat {
  def key = J.Key.pack (replicate 300 'a')
  def default = 0u64
}
module R = J.Record.Make (J.Record.Succ Field J.Record.Zero)
entry main (n:i64) =
  let xs = "{\"" ++ replicate n 'a' ++ "\":5}"
  in match R.obs (reduce R.op R.ne (map R.gen xs))
     case #some (v,()) -> (true,v)
     case #none -> (false,0u64)
-- ==
-- input { 300i64 } output { true 5u64 }
-- input { 253i64 } output { false 0u64 }
-- input { 255i64 } output { false 0u64 }
