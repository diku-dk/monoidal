import "../monoidal"
import "../monoidal_json"

open monoidal
open monoidal_json
module K = packed_key {def pred (_:u8) = true}
module Letters = packed_key {def pred (c:u8) = c >= 'a' && c <= 'z'}
module Pair = delim_prod K (decimal_try f64)

def id_key = Key.pack "id"
def score_key = Key.pack "score"
def colon (c:u8) : del u8 = if c == ':' then #Del c else #E c

entry packed (xs:[]u8) : (bool,bool) =
  match K.obs (reduce K.op K.ne (map K.gen xs))
  case #none -> (false,false)
  case #some w -> (true,Key.equal w (Key.pack xs))

entry constant (xs:[]u8) : bool =
  let k = Key.pack xs
  in match K.obs (reduce K.op K.ne (map K.gen xs))
     case #some v -> Key.equal k v
     case _ -> false

entry key_equal (xs:[]u8) (ys:[]u8) : bool = Key.equal (Key.pack xs) (Key.pack ys)

def key_code (k:Key.t) : i64 =
  if Key.equal k id_key then 1
  else if Key.equal k score_key then 2
  else if Key.equal k (Key.pack "") then 0
  else -1

entry pair (xs:[]u8) : (bool,i64,f64) =
  match Pair.obs (reduce Pair.op Pair.ne (map (Pair.gen <-< colon) xs))
  case #some (#some k,#some v) -> (true,key_code k,v)
  case _ -> (false,0,0)

-- Exact nonnegative i64 parser for up to 18 digits, including leading zeros.
-- Invalid characters are sanitised before nat.gen; validity is independent.
module Digits = with_gen (monoidal.nat i64) {
  type i = u8
  def gen (c:u8) = if c >= '0' && c <= '9' then c else '0'
}
module Valid = with_gen all {
  type i = u8
  def gen (c:u8) = c >= '0' && c <= '9'
}
module IntParts = dup {type i=u8}
  (prod Digits (dup {type i=u8} (prod Valid (count {type i=u8}))))
module Integer = with_obs IntParts {
  type o = opt i64
  def obs (x:IntParts.o) : o =
    let (v,(ok,n)) = x
    in if ok && n > 0 && n <= 18 then #some v else #none
}
module Number = dup {type i=u8} (prod Integer (decimal_try f64))
module Association = delim_prod K Number

-- Failure is separate from missing fields. Last assignment wins.
module Fields = {
  type t = opt (opt i64,opt f64)
  type i = del Association.o
  type o = opt {id:i64,score:f64}
  def ne : t = #some (#none,#none)
  def gen (x:i) : t =
    match x
    case #Del _ -> ne
    case #E (#some (#some k,(iv,fv))) ->
      if Key.equal k id_key then
        match iv case #some v -> #some (#some v,#none) case _ -> #none
      else if Key.equal k score_key then
        match fv case #some v -> #some (#none,#some v) case _ -> #none
      else #none
    case _ -> #none
  def choose 'a (x:opt a) (y:opt a) =
    match y case #none -> x case _ -> y
  def op (x:t) (y:t) : t =
    match (x,y)
    case (#some (a,b),#some (c,d)) -> #some (choose a c,choose b d)
    case _ -> #none
  def obs (x:t) : o =
    match x
    case #none -> #none
    case #some (i,s) ->
      #some {id = match i case #some v -> v case _ -> 0,
             score = match s case #some v -> v case _ -> 0}
}
module Rows = chunk Association Fields {def del_ign (_:u8) = false}
def row_gen c = Rows.gen (if c == ',' then #Del c else #E (colon c))

entry row (xs:[]u8) : (bool,i64,f64) =
  match Rows.obs (reduce Rows.op Rows.ne (map row_gen xs))
  case #some r -> (true,r.id,r.score)
  case #none -> (false,0,0)

module Laws (M:monoid) = {
  def every 'a (p:a -> bool) (xs:[]a) = reduce (&&) true (map p xs)
  def check (eq:M.o -> M.o -> bool) (xs:[]M.i) =
    let parts = map M.gen xs
    let fold ys = reduce M.op M.ne ys
    let expected = M.obs (fold parts)
    in every (\i -> every (\j ->
      let a = fold parts[:i]
      let b = fold parts[i:j]
      let c = fold parts[j:]
      let l = M.op (M.op a b) c
      let r = M.op a (M.op b c)
      in eq (M.obs l) expected && eq (M.obs r) expected &&
         eq (M.obs (M.op M.ne l)) expected &&
         eq (M.obs (M.op r M.ne)) expected)
      (iota (length xs-i+1) |> map (+i))) (iota (length xs+1))
}
module KL = Laws K
module LL = Laws Letters
module PL = Laws Pair
module RL = Laws Rows
def same_key (a:opt Key.t) (b:opt Key.t) : bool = match (a,b)
  case (#some x,#some y) -> Key.equal x y
  case (#none,#none) -> true
  case _ -> false
def same_pair (a:Pair.o) (b:Pair.o) : bool = match (a,b)
  case (#some (k,x),#some (l,y)) -> same_key k l && x == y
  case (#none,#none) -> true
  case _ -> false
entry laws (xs:[]u8) : bool =
  KL.check same_key xs && LL.check same_key xs && PL.check same_pair (map colon xs) &&
  RL.check (==) (map (\c -> if c == ',' then #Del c else #E (colon c)) xs)

entry letters (xs:[]u8) : (bool,bool) =
  match Letters.obs (reduce Letters.op Letters.ne (map Letters.gen xs))
  case #some k -> (true,Key.equal k (Key.pack xs))
  case #none -> (false,false)

-- ==
-- entry: letters
-- input { "" } output { true true }
-- input { "id" } output { true true }
-- input { "abcdefg" } output { true true }
-- input { "abcdefgh" } output { false false }
-- input { "!id" } output { false false }
-- input { "i!d" } output { false false }
-- input { "id!" } output { false false }
-- input { "ID" } output { false false }
-- input { [0u8] } output { false false }

-- ==
-- entry: packed
-- input { "" } output { true true }
-- input { "id" } output { true true }
-- input { "abcdefgh" } output { false false }
-- input { "abcdefg" } output { true true }
-- input { [0u8,0u8] } output { true true }

-- ==
-- entry: constant
-- input { "id" } output { true }
-- input { "" } output { true }
-- input { "abcdefg" } output { true }
-- input { "abcdefgh" } error: .*

-- ==
-- entry: pair
-- input { "score:5.2" } output { true 2i64 5.2f64 }
-- input { "id:23" } output { true 1i64 23f64 }
-- input { ":5" } output { true 0i64 5f64 }
-- input { "score:" } output { false 0i64 0f64 }
-- input { "score5.2" } output { false 0i64 0f64 }
-- input { "score::5.2" } output { false 0i64 0f64 }
-- input { "abcdefgh:5" } output { false 0i64 0f64 }

-- ==
-- entry: row
-- input { "id:7,score:5.2" } output { true 7i64 5.2f64 }
-- input { "score:12.75,id:123456789012345678" } output { true 123456789012345678i64 12.75f64 }
-- input { "score:-12.75" } output { true 0i64 -12.75f64 }
-- input { "id:42" } output { true 42i64 0f64 }
-- input { "id:7,id:0,score:5.2,score:0" } output { true 0i64 0f64 }
-- input { "id:1.5" } output { false 0i64 0f64 }
-- input { "other:5" } output { false 0i64 0f64 }
-- input { "id:1,,score:2" } output { false 0i64 0f64 }
-- input { "id:1," } output { false 0i64 0f64 }
-- input { "" } output { false 0i64 0f64 }

-- ==
-- entry: laws
-- input { "!id" } output { true }
-- input { "i!d" } output { true }
-- input { "id!" } output { true }
-- input { "" } output { true }
-- input { "abcdefg" } output { true }
-- input { "abcdefgh" } output { true }
-- input { ":" } output { true }
-- input { "::" } output { true }
-- input { "score:5.2" } output { true }
-- input { "id:7,score:5.25" } output { true }
-- input { "score:12.75,id:12345678" } output { true }
-- input { "abcdefgh:12" } output { true }
-- input { "id:7,id:0" } output { true }

-- ==
-- entry: key_equal
-- input { "id" "id" } output { true }
-- input { "id" "score" } output { false }
-- input { "" "" } output { true }
-- input { "id" "di" } output { false }
-- input { [0u8] [0u8,0u8] } output { false }
-- input { "abcdefg" "abcdefg" } output { true }
