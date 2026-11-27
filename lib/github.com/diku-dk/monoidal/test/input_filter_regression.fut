import "../monoidal"
open monoidal
module Sum = sum i64
module Inputs = input_filter Sum {def pred (x:i64) = x > 0}
module Output = filter Sum {def pred (x:i64) = x > 0}
-- Name abstract-summary instances before passing them to input_filter:
-- anonymous instances trigger a monomorphisation error in Futhark nightly.
module Multiplication = mul i64
module Product = input_filter Multiplication {def pred (x:i64) = x > 0}
entry compare_filters (xs:[]i64) : (i64,i64,i64) =
  (Inputs.obs (reduce Inputs.op Inputs.ne (map Inputs.gen xs)),
   Output.obs (reduce Output.op Output.ne (map Output.gen xs)),
   Product.obs (reduce Product.op Product.ne (map Product.gen xs)))

-- Type compatibility checks that input_filter preserves the base summary.
entry identity (xs:[]i64) : bool =
  let s = reduce Inputs.op Inputs.ne (map Inputs.gen xs)
  in Sum.obs (Sum.op Inputs.ne s) == Inputs.obs s &&
     Sum.obs (Sum.op s Inputs.ne) == Inputs.obs s

module Count = count {type i=i64}
module PositiveCount = input_filter Count {def pred (x:i64) = x > 0}
entry count_positive (xs:[]i64) =
  PositiveCount.obs (reduce PositiveCount.op PositiveCount.ne (map PositiveCount.gen xs))

-- Noncommutative aggregation: filtering must preserve input order.
module Digits = input_filter (nat u64) {def pred (c:u8) = c >= '0' && c <= '9'}
entry digits (xs:[]u8) = Digits.obs (reduce Digits.op Digits.ne (map Digits.gen xs))

-- A rejected value is syntactically present even though it contributes ne.
module List = separated Inputs {def delimiter:u8=','}
entry list (xs:[]u8) : (bool,i64) =
  let gen (c:u8) : List.t = List.gen (
    if c == ',' then #Raw c
    else if c == 'p' then #Nested (#some 3i64)
    else if c == 'n' then #Nested (#some (-2i64))
    else #Nested #none)
  in match List.obs (reduce List.op List.ne (map gen xs))
     case #some v -> (true,v)
     case _ -> (false,0)

-- ==
-- entry: compare_filters
-- input { [-5i64,3i64] } output { 3i64 0i64 3i64 }
-- input { [-1i64,3i64] } output { 3i64 2i64 3i64 }
-- input { [-2i64,0i64] } output { 0i64 0i64 1i64 }
-- input { [2i64,3i64] } output { 5i64 5i64 6i64 }
-- input { empty([0]i64) } output { 0i64 0i64 1i64 }

-- ==
-- entry: identity
-- input { [-5i64,3i64,7i64] } output { true }
-- input { empty([0]i64) } output { true }

-- ==
-- entry: count_positive
-- input { [-1i64,0i64,7i64,3i64] } output { 2i64 }

-- ==
-- entry: digits
-- input { "1x2y3" } output { 123u64 }
-- input { "xyz" } output { 0u64 }

-- ==
-- entry: list
-- input { "" } output { true 0i64 }
-- input { "n" } output { true 0i64 }
-- input { "n,n" } output { true 0i64 }
-- input { "n,p,n,p" } output { true 6i64 }
-- input { "nn" } output { false 0i64 }
-- input { "n," } output { false 0i64 }
-- input { ",n" } output { false 0i64 }
-- input { "n,,n" } output { false 0i64 }
-- input { "n,x" } output { false 0i64 }
