import "majority"

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
