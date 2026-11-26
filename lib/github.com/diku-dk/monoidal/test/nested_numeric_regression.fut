-- | ignore

import "../monoidal"
module D = monoidal.decimal_nested_try f64
module F = monoidal.float_nested_try f64
-- Total test model of generic nestable, with option-valued observation.
module Ref (R:monoid with i=u8 with o=opt f64) = {
  type t = #NE | #M R.t | #V f64 | #Fail
  type i = nest u8 f64
  type o = opt f64
  def ne : t = #NE
  def op (x:t) (y:t) : t = match (x,y)
    case (#Fail,_) -> #Fail
    case (_,#Fail) -> #Fail
    case (#NE,_) -> y
    case (_,#NE) -> x
    case (#M a,#M b) -> #M (R.op a b)
    case _ -> #Fail
  def gen (x:i) : t = match x
    case #Raw c -> #M (R.gen c)
    case #Nested v -> #V v
  def obs (x:t) : o = match x
    case #NE -> R.obs R.ne
    case #M a -> R.obs a
    case #V v -> #some v
    case #Fail -> #none
}
def all f xs = reduce (&&) true (map f xs)
def same (a:opt f64) (b:opt f64) = match (a,b)
  case (#none,#none) -> true
  case (#some x,#some y) -> f64.abs (x-y) <= 1e-12 * f64.max 1 (f64.abs x)
  case _ -> false
module Check (P:monoid with i=nest u8 f64 with o=opt f64)
             (R:monoid with i=u8 with o=opt f64) = {
  module B = Ref R
  def fold xs = loop s=P.ne for c in xs do P.op s (P.gen c)
  def check xs =
    let h=fold xs
    let ref=loop s=B.ne for c in xs do B.op s (B.gen c)
    let obs=P.obs h
    in same obs (B.obs ref) && same obs (P.obs (P.op P.ne h)) &&
       same obs (P.obs (P.op h P.ne)) &&
       same obs (P.obs (reduce P.op P.ne (map P.gen xs))) &&
       all (\i -> all (\j ->
         let a=fold xs[:i]
         let b=fold xs[i:i+j]
         let c=fold xs[i+j:]
         in same obs (P.obs (P.op (P.op a b) c)) &&
            same obs (P.obs (P.op a (P.op b c))))
         (iota (length xs-i+1))) (iota (length xs+1))
}
module DC = Check D (monoidal.decimal_try f64)
module FC = Check F (monoidal.float_try f64)
entry exhaustive (_:bool) =
  let alphabet : []nest u8 f64 = [#Raw '0',#Raw '7',#Raw '.',#Raw '-',#Raw 'x',#Nested 2.5]
  in all (\n ->
    let count=loop p=1i64 for _i<n do p*6
    in all (\code ->
      let (_,xs)=loop (k,xs)=(code,replicate n (#Raw '0')) for i<n do
        (k/6,xs with [i]=alphabet[k%6])
      in DC.check xs && FC.check xs) (iota count)) (iota 6)
entry long (xs:[]u8) = DC.check (map (\c -> #Raw c) xs) && FC.check (map (\c -> #Raw c) xs)
entry bits (_:bool) =
  all (\bits ->
    let v=f64.from_bits bits
    let d=D.gen (#Nested v)
    let f=F.gen (#Nested v)
    let eq x = match x case #some y -> f64.to_bits y == bits case _ -> false
    in eq (D.obs (D.op D.ne (D.op d D.ne))) &&
       eq (F.obs (F.op F.ne (F.op f F.ne))))
    [0u64,0x8000000000000000u64,0x7ff0000000000000u64,
     0xfff0000000000000u64,0x7ff8000000001234u64,0x3ff4000000000000u64]

-- ==
-- entry: exhaustive bits
-- input { true }
-- output { true }

-- ==
-- entry: long
-- input { "-123456789012345.678" }
-- output { true }
-- input { "1234567890123456789" }
-- output { true }
-- input { "-0000000000000000000" }
-- output { true }
