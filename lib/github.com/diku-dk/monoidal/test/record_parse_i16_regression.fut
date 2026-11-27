import "record_testing"
entry main = parse_i16

-- ==
-- entry: main
-- input { "32767" } output { true 32767i16 }
-- input { "32768" } output { false 0i16 }
-- input { "-32768" } output { true -32768i16 }
-- input { "-32769" } output { false 0i16 }
