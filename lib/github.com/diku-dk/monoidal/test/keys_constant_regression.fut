import "keys_testing"
entry main = constant

-- ==
-- entry: main
-- input { "id" } output { true }
-- input { "" } output { true }
-- input { "abcdefg" } output { true }
-- input { "abcdefgh" } error: .*
