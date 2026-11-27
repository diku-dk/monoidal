import "record_testing"
entry main = integer

-- ==
-- entry: main
-- input { "0" } output { true 0i64 }
-- input { "-0" } output { true 0i64 }
-- input { "-123456789012345678" } output { true -123456789012345678i64 }
-- input { "9223372036854775807" } output { true 9223372036854775807i64 }
-- input { "-9223372036854775808" } output { true -9223372036854775808i64 }
-- input { "9223372036854775808" } output { false 0i64 }
-- input { "-9223372036854775809" } output { false 0i64 }
-- input { "9999999999999999999" } output { false 0i64 }
-- input { "00000000000000000000" } output { true 0i64 }
-- input { "000000000000000000000" } output { false 0i64 }
-- input { "" } output { false 0i64 }
-- input { "-" } output { false 0i64 }
-- input { "--1" } output { false 0i64 }
-- input { "1-" } output { false 0i64 }
-- input { "+1" } output { false 0i64 }
-- input { "1.0" } output { false 0i64 }
