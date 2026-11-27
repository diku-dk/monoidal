import "../monoidal"
import "../monoidal_json"
module J = monoidal_json
module A = J.field {type t=u64} J.nat {
  def key = J.Key.pack [1u8,132]
  def default = 0u64
}
module B = J.field {type t=u64} J.nat {
  def key = J.Key.pack [2u8,1]
  def default = 0u64
}
module R = J.Record.Make (J.Record.Succ A (J.Record.Succ B J.Record.Zero))
entry main (xs:[]u8) = match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some _ -> true case _ -> false
-- ==
-- input { "{}" } error: .*
