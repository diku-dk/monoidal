import "record_testing"
entry main = parse_u64

-- ==
-- entry: main
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { false 0u64 }
-- input { "99999999999999999999" } output { false 0u64 }
-- input { "10000000000000000000" } output { true 10000000000000000000u64 }
-- input { "00000000000000000001" } output { true 1u64 }
-- input { "000000000000000000001" } output { false 0u64 }
-- input { "-0" } output { false 0u64 }
-- input { "-1" } output { false 0u64 }
-- input { "" } output { false 0u64 }
