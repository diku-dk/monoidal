-- | ignore

import "../monoidal"

module Regression = {
  open monoidal
  module Inner = {
    type t = i64
    type i = i64
    type o = i64
    def ne = 0i64
    def op (x:t) (y:t) = x+y
    def gen (x:i) = x
    def obs (x:t) = x
  }
  module Outer = {
    open Inner
    type i = nest i64 i64
    def gen (x:i) = match x case #Raw v -> v case #Nested v -> v
  }
  module M = parens Inner Outer {
    def left (c:u8) = c == '('
    def right (c:u8) = c == ')'
  }
  def token (c:u8) : del i64 = if c == '(' || c == ')' then #Del c else #E 7i64
  def summary xs = loop s = M.ne for x in xs do M.op s (M.gen (token x))
  def all f xs = reduce (&&) true (map f xs)
  def splits [n] (xs:[n]u8) =
    all (\i -> all (\j ->
      let x = summary xs[:i]
      let y = summary xs[i:j]
      let z = summary xs[j:]
      in M.op (M.op x y) z == M.op x (M.op y z))
      (iota (n-i+1) |> map (+i))) (iota (n+1))
}

-- Compare complete summaries, not just their observations.
entry regression (_:bool) : (bool,i64,i64) =
  let x = Regression.summary "7"
  let l = Regression.summary "("
  let r = Regression.summary ")"
  let lhs = Regression.M.op (Regression.M.op x l) r
  let rhs = Regression.M.op x (Regression.M.op l r)
  in (lhs == rhs, Regression.M.obs lhs, Regression.M.obs rhs)

entry split_laws [n] (xs:[n]u8) : bool = Regression.splits xs

-- Exhaustively compare the tag-only dispatch with the previous depth guard,
-- including failure and arbitrary payloads, not merely generated fragments.
entry depth_guard_equivalent (_:bool) : bool =
  let forms : []Regression.M.t =
    [#Fail, #A (2,3), #Closed 5,
     #L (7,11), #R (13,17), #B (19,23,29)]
  let guarded x y = match (x,y)
    case (#Fail, _) -> #Fail
    case (_, #Fail) -> #Fail
    case (x,y) ->
      let (xl,xh,xn) = Regression.M.depth x
      let (yl,yh,_) = Regression.M.depth y
      in if i64.max xh (xn+yh) - i64.min xl (xn+yl) > 1 then #Fail
         else Regression.M.combine_forms x y
  in reduce (&&) true (map (\x -> reduce (&&) true
       (map (\y -> Regression.M.op x y == guarded x y) forms)) forms)

-- ==
-- entry: depth_guard_equivalent
-- input { true }
-- output { true }

-- All 364 strings of length at most five over an atom and the two
-- parentheses, including malformed fragments and depth overflow.
entry exhaustive (_:bool) : bool =
  let alphabet = ['7', '(', ')'] : []u8
  let check_length (n:i64) =
    let count = loop p = 1i64 for _i < n do p*3
    in reduce (&&) true (map (\code ->
      let (_,xs) = loop (k,xs) = (code, replicate n '7') for i < n do
        (k/3, xs with [i] = alphabet[k%3])
      let s = Regression.summary xs
      in Regression.splits xs &&
         Regression.M.op Regression.M.ne s == s &&
         Regression.M.op s Regression.M.ne == s)
      (iota count))
  in reduce (&&) true (map check_length (iota 6))

-- Check the new representation and preservation of nesting rejection.
entry representation (_:bool) : bool =
  let completed = match Regression.summary "7(7)7"
                  case #Closed x -> x == 21
                  case _ -> false
  let rejected = match Regression.summary "((7))"
                 case #Fail -> true
                 case _ -> false
  in completed && rejected

-- ==
-- entry: exhaustive
-- input { true }
-- output { true }

-- ==
-- entry: representation
-- input { true }
-- output { true }

-- ==
-- entry: regression
-- input { true }
-- output { true 7i64 7i64 }

-- ==
-- entry: split_laws
-- input { "" }
-- output { true }
-- input { "777" }
-- output { true }
-- input { "7()" }
-- output { true }
-- input { "()7" }
-- output { true }
-- input { "7(77)7" }
-- output { true }
-- input { "(7)(77)" }
-- output { true }
-- input { ")7(" }
-- output { true }
-- input { "((7))" }
-- output { true }
