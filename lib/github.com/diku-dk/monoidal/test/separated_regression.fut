import "../monoidal"
module Agg = {
  type t = (u64,u64)
  type i = u64
  type o = t
  def ne : t = (0,1)
  def op ((a,p):t) ((b,q):t) : t = (a*q+b,p*q)
  def gen (v:i) : t = (v,17)
  def obs (x:t) = x
}
module S = monoidal.separated Agg {def delimiter:u8=','}
def token (x:i64) : S.i = match x
  case 0 -> #Raw ','
  case 1 -> #Nested (#some 1u64)
  case 2 -> #Nested (#some 2u64)
  case 3 -> #Nested #none
  case _ -> #Raw '!'
def fold (xs:[]S.t) = reduce S.op S.ne xs
def result (x:S.t) = match S.obs x
  case #none -> (false,0u64,0u64)
  case #some (h,p) -> (true,h,p)
-- Independent sequential recogniser, including defaults for the empty array.
def reference (tokens:[]i64) =
  let (valid,need,acc) = loop (valid,need,acc) = (true,true,Agg.ne)
    for c in tokens do
      if c == 0 then (valid && !need,true,acc)
      else if c == 1 || c == 2 then
        (valid && need,false,Agg.op acc (Agg.gen (u64.i64 c)))
      else (false,need,acc)
  in if length tokens == 0 || (valid && !need)
     then (true,acc.0,acc.1) else (false,0u64,0u64)

-- Tokens: comma=0, values=1/2, invalid nested=3, invalid raw=4.
def check (tokens:[]i64) =
    let n = length tokens
    let xs = map (S.gen <-< token) tokens
    let expected = result (fold xs)
    let laws = expected == reference tokens &&
      result (S.op S.ne (fold xs)) == expected &&
      result (S.op (fold xs) S.ne) == expected &&
      all (\i -> all (\j ->
      let a=fold xs[:i]
      let b=fold xs[i:j]
      let c=fold xs[j:]
      in result (S.op (S.op a b) c) == expected &&
         result (S.op a (S.op b c)) == expected)
      (map (+i) (iota (n-i+1)))) (iota (n+1))
    in laws

entry main = check
#[prop(size(8))]
entry generated (codes:[]u8) = check (map (\c -> i64.u8 c % 5) codes)

-- ==
-- entry: main
-- input { empty([0]i64) } output { true }
-- input { [1i64] } output { true }
-- input { [1i64,0,2] } output { true }
-- input { [2i64,0,1,0,2] } output { true }
-- input { [0i64] } output { true }
-- input { [0i64,1] } output { true }
-- input { [1i64,0] } output { true }
-- input { [1i64,2] } output { true }
-- input { [1i64,0,0,2] } output { true }
-- input { [3i64] } output { true }
-- input { [1i64,0,3] } output { true }
-- input { [4i64] } output { true }

-- ==
-- property: generated
