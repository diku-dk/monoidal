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
