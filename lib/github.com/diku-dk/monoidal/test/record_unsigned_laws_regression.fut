import "record_testing"
entry main = unsigned_laws

-- ==
-- entry: main
-- input { "18446744073709551615" } output { true }
-- input { "18446744073709551616" } output { true }
-- input { "99999999999999999999" } output { true }
-- input { "00000000000000000001" } output { true }
-- input { "000000000000000000001" } output { true }
-- input { "-0" } output { true }
