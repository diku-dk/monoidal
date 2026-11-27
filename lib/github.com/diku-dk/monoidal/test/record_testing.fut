-- | ignore

import "../monoidal"
import "../monoidal_json"
open monoidal
open monoidal_json
module Int = int_try i64

module Check (Y:integral) = {
  module M = int_try Y
  def parse (xs:[]u8) : (bool,Y.t) =
    match M.obs (reduce M.op M.ne (map M.gen xs))
    case #some v -> (true,v)
    case _ -> (false,Y.i64 0)
  def laws (xs:[]u8) : bool =
    let parts = map M.gen xs
    let fold ys = reduce M.op M.ne ys
    let expected = fold parts
    in reduce (&&) true (map (\i ->
      reduce (&&) true (map (\j ->
        let a = fold parts[:i]
        let b = fold parts[i:j]
        let c = fold parts[j:]
        let l = M.op (M.op a b) c
        let r = M.op a (M.op b c)
        in l == expected && r == expected &&
           M.op M.ne l == l && M.op r M.ne == r)
        (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))
}
module I8 = Check i8
module I16 = Check i16
module I32 = Check i32
module U8 = Check u8
module U16 = Check u16
module U32 = Check u32
module U64 = Check u64
def parse_i8 = I8.parse
def parse_i16 = I16.parse
def parse_i32 = I32.parse
def parse_u8 = U8.parse
def parse_u16 = U16.parse
def parse_u32 = U32.parse
def parse_u64 = U64.parse
def unsigned_laws = U64.laws

def integer (xs:[]u8) : (bool,i64) =
  match Int.obs (reduce Int.op Int.ne (map Int.gen xs))
  case #some v -> (true,v)
  case _ -> (false,0)

def integer_laws (xs:[]u8) : bool =
  let parts = map Int.gen xs
  let fold ys = reduce Int.op Int.ne ys
  let expected = fold parts
  in reduce (&&) true (map (\i ->
    reduce (&&) true (map (\j ->
      let a = fold parts[:i]
      let b = fold parts[i:j]
      let c = fold parts[j:]
      let l = Int.op (Int.op a b) c
      let r = Int.op a (Int.op b c)
      in l == expected && r == expected &&
         Int.op Int.ne l == l && Int.op r Int.ne == r)
      (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))

-- Different names, types, defaults, and field order: not hardwired to JSON.
module X = field {type t=f64} (float_try f64) {
  def key = Key.pack "x"
  def default = 1.5f64
}
module Y = field {type t=i64} (int_try i64) {
  def key = Key.pack "y"
  def default = 9i64
}
module R = monoidal_json.Record.Make
  (monoidal_json.Record.Succ X
    (monoidal_json.Record.Succ Y monoidal_json.Record.Zero))
def record (xs:[]u8) : (bool,f64,i64) =
  match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some (a,(b,())) -> (true,a,b)
  case _ -> (false,0,0)

module S = separated (sum i64) {def delimiter:u8=';'}
def symbol (c:u8) : S.i =
  if c >= '0' && c <= '9' then #Nested (#some (i64.u8 (c-'0')))
  else #Raw c
module Bytes = with_gen S {type i=u8 def gen = symbol}
module Wrapped = enclosed {type t=i64} Bytes {def left:u8='(' def right:u8=')'}
def separated_list (xs:[]u8) : (bool,i64) =
  match Wrapped.obs (reduce Wrapped.op Wrapped.ne (map Wrapped.gen xs))
  case #some v -> (true,v)
  case _ -> (false,0)

-- Configuration errors are distinct from malformed input.
module Same = monoidal_json.Record.Make
  (monoidal_json.Record.Succ Y
    (monoidal_json.Record.Succ Y monoidal_json.Record.Zero))
def duplicate_keys (xs:[]u8) : bool =
  match Same.obs (reduce Same.op Same.ne (map Same.gen xs))
  case #some _ -> true case _ -> false
