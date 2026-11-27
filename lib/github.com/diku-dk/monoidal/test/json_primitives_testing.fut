-- | ignore

import "../monoidal"
import "../monoidal_json"
module M = monoidal
module J = monoidal_json

def boolean (xs:[]u8) : (bool,bool) =
  match J.bool.obs (reduce J.bool.op J.bool.ne (map J.bool.gen xs))
  case #some v -> (true,v)
  case #none -> (false,false)
def natural (xs:[]u8) : (bool,u64) =
  match J.nat.obs (reduce J.nat.op J.nat.ne (map J.nat.gen xs))
  case #some v -> (true,v)
  case #none -> (false,0)
def number (xs:[]u8) : (bool,f64) =
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
def record (xs:[]u8) : (bool,bool,u64) =
  match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some (a,(n,())) -> (true,a,n)
  case #none -> (false,false,0)

def boolean_splits (xs:[]u8) : bool =
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
