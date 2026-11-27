import "nat_try_testing"
entry main = parse_u8

-- ==
-- entry: main
-- input { "255" } output { true 255u8 }
-- input { "256" } output { true 0u8 }
-- input { "0000000" } output { true 0u8 }
-- input { "00000000" } output { false 0u8 }
-- input { "12345678" } output { false 0u8 }
