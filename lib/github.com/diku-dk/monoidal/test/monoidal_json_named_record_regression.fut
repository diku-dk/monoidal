import "monoidal_json_testing"
entry main = named_record

-- ==
-- entry: main
-- input { "{\"b\":2.5,\"a\":12}" } output { true 12u64 2.5f64 }
-- input { "{\"a\":0}" } output { true 0u64 1.5f64 }
-- input { "{\"a\":bad}" } output { false 0u64 0f64 }
-- input { "{}" } output { false 0u64 0f64 }
