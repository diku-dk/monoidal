-- | ignore

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
def main (xs:[]u8) = flatten (RR.run xs)
def one (xs:[]u8) = match RO.run xs
  case #some (v,()) -> (true,v)
  case #none -> (false,0u64)
def zero (xs:[]u8) = match RZ.run xs case #some _ -> true case _ -> false
def four (xs:[]u8) = match RF.run xs
  case #some (extra,(id,(score,(active,())))) -> (extra,true,id,score,active)
  case #none -> (0u64,false,0u64,0f64,false)
def array_count (xs:[]u8) = match RQ.run xs
  case #some n -> (true,n)
  case #none -> (false,0i64)
