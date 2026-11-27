-- | ignore

import "../monoidal"
open monoidal
module Check (Y:integral) = {
  module M = nat_try Y
  def parse (xs:[]u8) : (bool,Y.t) =
    match M.obs (reduce M.op M.ne (map M.gen xs))
    case #some v -> (true,v)
    case _ -> (false,Y.i64 0)
  def laws (xs:[]u8) : bool =
    let eq ((a,b):M.t) ((c,d):M.t) = Y.(a == c && b == d)
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
        in eq l expected && eq r expected &&
           eq (M.op M.ne l) l && eq (M.op r M.ne) r)
        (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))
}
module U64 = Check u64
module U8 = Check u8
module I8 = Check i8
def parse = U64.parse
def parse_u8 = U8.parse
def parse_i8 = I8.parse
def laws (xs:[]u8) = U64.laws xs && U8.laws xs && I8.laws xs
def zeros (n:i64) = U64.parse (replicate n '0')
def zero_laws (n:i64) = U64.laws (replicate n '0')
