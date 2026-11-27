import "nat_try_testing"
entry main = parse

-- ==
-- entry: main
-- input { "" } output { false 0u64 }
-- input { "0" } output { true 0u64 }
-- input { "0005" } output { true 5u64 }
-- input { "123456789012345678" } output { true 123456789012345678u64 }
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { true 0u64 }
-- input { "18446744073709551621" } output { true 5u64 }
-- input { "-0" } output { false 0u64 }
-- input { "-5" } output { false 0u64 }
-- input { "+5" } output { false 0u64 }
-- input { "5.0" } output { false 0u64 }
-- input { " 5" } output { false 0u64 }
-- input { "5 " } output { false 0u64 }
-- input { "12x34" } output { false 0u64 }
-- input { [0u8] } output { false 0u64 }
