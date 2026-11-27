import "record_testing"
entry main = integer_laws

-- ==
-- entry: main
-- input { "-9223372036854775808" } output { true }
-- input { "9223372036854775808" } output { true }
-- input { "00000000000000000000" } output { true }
-- input { "--1" } output { true }
-- input { "1-" } output { true }
-- input { "" } output { true }
