import "monoidal_json_testing"
entry main = record

-- ==
-- entry: main
-- input { "{\"a\":12,\"b\":3.25}" } output { true 12u64 3.25f64 }
-- input { "{\"b\":-2.5,\"a\":42}" } output { true 42u64 -2.5f64 }
-- input { "{\"a\":0}" } output { true 0u64 1.5f64 }
-- input { "{\"b\":0}" } output { true 7u64 0f64 }
-- input { "{\"a\":1,\"a\":2}" } output { true 2u64 1.5f64 }
-- input { "{}" } output { false 0u64 0f64 }
-- input { "{a:1}" } output { false 0u64 0f64 }
-- input { "{\"x\":1}" } output { false 0u64 0f64 }
-- input { "{\"a\":-1}" } output { false 0u64 0f64 }
-- input { "{\"a\":1,}" } output { false 0u64 0f64 }
-- input { "\"a\":1" } output { false 0u64 0f64 }
-- input { "{\"a\":1" } output { false 0u64 0f64 }
-- input { "{{\"a\":1}}" } output { false 0u64 0f64 }
