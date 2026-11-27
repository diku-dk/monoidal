import "decimal_testing"
entry main = splits

-- ==
-- entry: main
-- input { "-123456789012345.678" }
-- output { true }
-- input { "1234567890123456789" }
-- output { true }
-- input { "-0000000000000000000" }
-- output { true }
-- input { "123456789.012345678." }
-- output { true }
