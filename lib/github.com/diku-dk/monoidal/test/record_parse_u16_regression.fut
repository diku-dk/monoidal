import "record_testing"
entry main = parse_u16

-- ==
-- entry: main
-- input { "65535" } output { true 65535u16 }
-- input { "65536" } output { false 0u16 }
-- input { "-0" } output { false 0u16 }
