import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests or_example.M

entry test_or_splits (xs:[]u8) : bool = Check.splits or_example.same xs

-- ==
-- entry: test_or_splits
-- input { "12.34" }
-- output { true }
-- input { "12,34" }
-- output { true }
-- input { "1.2.3" }
-- output { true }

