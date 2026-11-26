import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests parenthesised_sumofproducts.T2

entry test_parenthesised_sumofproducts2_association (xs:[]u8) : bool = Check.associations (==) xs

-- ==
-- entry: test_parenthesised_sumofproducts2_association
-- input { "2*(3+(4*5))" }
-- output { true }
-- input { "((2+3)*4)" }
-- output { true }
-- input { "(2+(3*4))*(5+(6*7))" }
-- output { true }

