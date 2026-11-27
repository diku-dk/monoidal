import "keys_testing"
entry main = pair

-- ==
-- entry: main
-- input { "score:5.2" } output { true 2i64 5.2f64 }
-- input { "id:23" } output { true 1i64 23f64 }
-- input { ":5" } output { true 0i64 5f64 }
-- input { "score:" } output { false 0i64 0f64 }
-- input { "score5.2" } output { false 0i64 0f64 }
-- input { "score::5.2" } output { false 0i64 0f64 }
-- input { "abcdefgh:5" } output { true -1i64 5f64 }
