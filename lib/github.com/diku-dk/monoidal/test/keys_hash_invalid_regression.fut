import "keys_hash_testing"
entry main (a:[]u8) (b:[]u8) (c:[]u8) = laws a b c
-- ==
-- input { "" "" "" } output { true }
-- input { "long_" "field_" "name" } output { true }
-- input { [255u8] "" "a" } output { true }
-- input { "a" [255u8] "b" } output { true }
-- input { "a" "" [255u8] } output { true }
