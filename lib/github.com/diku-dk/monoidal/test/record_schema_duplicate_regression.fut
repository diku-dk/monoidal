import "../monoidal"
import "../monoidal_json"
module J = monoidal_json
module A = J.field {type t=u64} J.nat {
  def key = J.Key.pack "id"
  def default = 0u64
}
module B = J.field {type t=bool} J.bool {
  def key = J.Key.pack "active"
  def default = false
}
module R = J.Record.Make (J.Record.Succ A (J.Record.Succ B (J.Record.Succ A J.Record.Zero)))
entry main (xs:[]u8) = match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some _ -> true case _ -> false
-- ==
-- input { "{}" } error: .*
-- input { "{\"id\":1}" } error: .*
