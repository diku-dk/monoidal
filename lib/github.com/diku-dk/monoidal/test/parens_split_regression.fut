import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests parenthesised_sumofproducts.T

entry test_parenthesised_sumofproducts_splits (xs:[]u8) : bool = Check.splits (==) xs

-- ==
-- entry: test_parenthesised_sumofproducts_splits
-- input { "34" }
-- output { true }
-- input { "(34)" }
-- output { true }
-- input { "2*(3+4)+5" }
-- output { true }
-- input { "(2+3)*(4+5)" }
-- output { true }
-- input { "(2*3)+(4*5)" }
-- output { true }
-- input { "1+2*(3+4)*5+6" }
-- output { true }
-- input { "2+3*(4+5)+6*(7+8)+9" }
-- output { true }
-- input { "12*(34+56)+78" }
-- output { true }
-- input { "(12+34)*(56+78)" }
-- output { true }
-- input { "100+25*(30+4)*2+7" }
-- output { true }
