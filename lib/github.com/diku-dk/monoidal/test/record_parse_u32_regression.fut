import "record_testing"
entry main = parse_u32

-- ==
-- entry: main
-- input { "4294967295" } output { true 4294967295u32 }
-- input { "4294967296" } output { false 0u32 }
-- input { "-0" } output { false 0u32 }
