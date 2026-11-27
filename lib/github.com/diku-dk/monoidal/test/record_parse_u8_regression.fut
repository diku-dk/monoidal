import "record_testing"
entry main = parse_u8

-- ==
-- entry: main
-- input { "255" } output { true 255u8 }
-- input { "256" } output { false 0u8 }
-- input { "-1" } output { false 0u8 }
-- input { "-0" } output { false 0u8 }
