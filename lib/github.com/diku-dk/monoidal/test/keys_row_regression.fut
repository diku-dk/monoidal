import "keys_testing"
entry main = row

-- ==
-- entry: main
-- input { "id:7,score:5.2" } output { true 7i64 5.2f64 }
-- input { "score:12.75,id:123456789012345678" } output { true 123456789012345678i64 12.75f64 }
-- input { "score:-12.75" } output { true 0i64 -12.75f64 }
-- input { "id:42" } output { true 42i64 0f64 }
-- input { "id:7,id:0,score:5.2,score:0" } output { true 0i64 0f64 }
-- input { "id:1.5" } output { false 0i64 0f64 }
-- input { "other:5" } output { false 0i64 0f64 }
-- input { "id:1,,score:2" } output { false 0i64 0f64 }
-- input { "id:1," } output { false 0i64 0f64 }
-- input { "" } output { false 0i64 0f64 }
