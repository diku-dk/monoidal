-- | ignore
import "parens_tuple_testing"
module C = Check R3
entry main (xs:[]u8) = C.check xs
-- ==
-- input { "" } output { true }
-- input { "ab" } output { true }
-- input { "()" } output { true }
-- input { "(ab)" } output { true }
-- input { "a(b)a" } output { true }
-- input { "(a)(b)" } output { true }
-- input { "(((ab)))" } output { true }
