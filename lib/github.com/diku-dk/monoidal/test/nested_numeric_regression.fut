import "nested_numeric_testing"
entry main = mixed

-- ==
-- entry: main
-- input { empty([0]i64) } output { true }
-- input { [0i64] } output { true }
-- input { [0i64,0] } output { true }
-- input { [48i64,0] } output { true }
-- input { [0i64,48] } output { true }
-- input { [45i64,55,46,48] } output { true }
-- input { [120i64] } output { true }
