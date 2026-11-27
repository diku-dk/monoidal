import "keys_testing"
entry main = packed

-- ==
-- entry: main
-- input { "" } output { true true }
-- input { "id" } output { true true }
-- input { "abcdefgh" } output { true true }
-- input { "abcdefg" } output { true true }
-- input { [0u8,0u8] } output { true true }
