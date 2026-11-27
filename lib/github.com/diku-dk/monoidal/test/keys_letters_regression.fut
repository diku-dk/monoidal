import "keys_testing"
entry main = letters

-- ==
-- entry: main
-- input { "" } output { true true }
-- input { "id" } output { true true }
-- input { "abcdefg" } output { true true }
-- input { "abcdefgh" } output { true true }
-- input { "!id" } output { false false }
-- input { "i!d" } output { false false }
-- input { "id!" } output { false false }
-- input { "ID" } output { false false }
-- input { [0u8] } output { false false }
