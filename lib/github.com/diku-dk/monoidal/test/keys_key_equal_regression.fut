import "keys_testing"
entry main = key_equal

-- ==
-- entry: main
-- input { "id" "id" } output { true }
-- input { "id" "score" } output { false }
-- input { "" "" } output { true }
-- input { "id" "di" } output { false }
-- input { [0u8] [0u8,0u8] } output { false }
-- input { "abcdefg" "abcdefg" } output { true }
