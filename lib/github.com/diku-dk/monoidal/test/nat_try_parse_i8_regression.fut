import "nat_try_testing"
entry main = parse_i8

-- ==
-- entry: main
-- input { "127" } output { true 127i8 }
-- input { "128" } output { true -128i8 }
-- input { "-1" } output { false 0i8 }
-- input { "00000000" } output { false 0i8 }
