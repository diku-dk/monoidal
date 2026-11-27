-- | ignore
import "parens_tuple_testing"
module C = Check R0
entry main (xs:[]u8) = C.check xs
-- ==
-- input { "" } output { true }
-- input { "ab" } output { true }
