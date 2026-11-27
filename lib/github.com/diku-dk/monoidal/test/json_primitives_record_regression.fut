import "json_primitives_testing"
entry main = record

-- ==
-- entry: main
-- input { "{\"active\":true,\"n\":12}" } output { true true 12u64 }
-- input { "{\"n\":2,\"active\":false}" } output { true false 2u64 }
-- input { "{\"n\":3}" } output { true false 3u64 }
-- input { "{\"active\":true,\"active\":false}" } output { true false 0u64 }
-- input { "{\"active\":TRUE}" } output { false false 0u64 }
-- input { "{\"active\":\"true\"}" } output { false false 0u64 }
-- input { "{\"active\":true,\"n\":bad}" } output { false false 0u64 }
