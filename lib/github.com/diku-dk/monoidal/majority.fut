-- | Boyer-Moore Majority Voting. Reduction using a non-monoid, guarded with a
-- count check to ensure correctness; see the paper Oleg Kiselyov. More Fun with
-- Monoids. 2026. https://okmij.org/ftp/Algorithms/monoid-fun.pdf

-- | Option type.
type opt 'a = #some a | #none

local
-- | Module type for majority voting.
module type majority = {
  type t

  -- | Returns `#some e` if `e` appears as an element in the input array a
  -- majority (> 50 percent) number of times. Returns `#none` otherwise.
  val majority [n] : [n]t -> opt t
}

-- | Parameterised module for majority voting.
module mk_majority (X : { type t val (==): t -> t -> bool })
       : majority with t = X.t = {
  type t = X.t
  type maj = (i64, t)
  def eq = (X.==)

  def maj (x1:maj) (x2:maj) : maj =
    let (c1,m1) = x1
    let (c2,m2) = x2
    in if c1 == 0 then x2
       else if c2 == 0 then x1
       else if eq m1 m2 then (c1+c2,m1)
       else if c1 >= c2 then (c1-c2,m1)
       else (c2-c1,m2)

  def count [n] (x:t) (xs:[n]t) : i64 =
    let ys = map (\y -> if eq y x then 1 else 0) xs
    in reduce (+) 0 ys

  def majority [n] (xs:[n]t) : opt t =
    if n == 0 then #none
    else let a = xs[0]
	 let maj0 : maj = (0,a)
	 let ys : [n](maj) = map (\x -> (1,x)) xs
	 let x = reduce maj maj0 ys |> (.1)
	 in if count x xs >= n / 2 then #some x else #none
}

module maj_i64 = mk_majority i64

entry test [n] (xs:[n]i64) : i64 =
  match maj_i64.majority xs
  case #none -> -1
  case #some x -> x

-- Tests of majority voting
-- ==
-- entry: test
-- input { [3i64,2,45,2,5,53,4,2,5,2,6,2,7,2,64,5,2,2,5,2,66,2,3,2,2,7,2,2,4,3,3,4] }
-- output { -1i64 }
-- input { [3i64,2,45,2,5,53,4,2,5,2,6,2,7,2,64,5,2,2,5,2,66,2,3,2,2,7,2,2,4,2,3,2,3,2,4] }
-- output { 2i64 }

def xs = [3,2,45,2,5,53,4,2,5,2,6,2,7,2,64,5,2,2,5,2,66,2,3,2,2,7,2,2i64,4,3,3,4]
def ys = [3,2,45,2,5,53,4,2,5,2,6,2,7,2,64,5,2,2,5,2,66,2,3,2,2,7,2,2i64,4,2,3,2,3,2,4]

def test1() : opt i64 = maj_i64.majority xs
def test2() : opt i64 = maj_i64.majority ys

def run_tests () : bool =
  test1() == #none && test2() == #some 2
