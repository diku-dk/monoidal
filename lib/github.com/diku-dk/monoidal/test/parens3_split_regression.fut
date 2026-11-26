import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests parenthesised_sumofproducts.T3

entry test_parenthesised_sumofproducts3_splits (xs:[]u8) : bool = Check.splits (==) xs

-- ==
-- entry: test_parenthesised_sumofproducts3_splits
-- input { "(((2+3)*4)+5)" }
-- output { true }
-- input { "2*(3+(4*(5+6)))" }
-- output { true }
-- input { "12*(34+(56*(2+3*4)))+78" }
-- output { true }
-- input { "12*(34+(56*(2+3)))+78" }
-- output { true }
