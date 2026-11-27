import "nat_try_testing"
entry main = laws

-- ==
-- entry: main
-- input { "" } output { true }
-- input { "0" } output { true }
-- input { "123456789" } output { true }
-- input { "18446744073709551615" } output { true }
-- input { "18446744073709551616" } output { true }
-- input { "12x34" } output { true }
-- input { "-0" } output { true }
