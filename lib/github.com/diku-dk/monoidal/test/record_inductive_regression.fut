import "record_inductive_testing"
entry main = main

-- ==
-- entry: main
-- input { "{\"id\":5,\"score\":2.5,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"id\":5,\"active\":false,\"score\":2.5}" } output { true 5u64 2.5f64 false }
-- input { "{\"score\":2.5,\"id\":5,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"score\":2.5,\"active\":false,\"id\":5}" } output { true 5u64 2.5f64 false }
-- input { "{\"active\":false,\"id\":5,\"score\":2.5}" } output { true 5u64 2.5f64 false }
-- input { "{\"active\":false,\"score\":2.5,\"id\":5}" } output { true 5u64 2.5f64 false }
-- input { "{}" } output { false 0u64 0f64 false }
-- input { "{\"active\":false}" } output { true 7u64 1.5f64 false }
-- input { "{\"id\":1,\"score\":2.5,\"id\":5,\"active\":true,\"active\":false}" } output { true 5u64 2.5f64 false }
-- input { "{\"id\":-1,\"id\":5}" } output { false 0u64 0f64 false }
-- input { "{\"active\":bad,\"active\":true}" } output { false 0u64 0f64 false }
-- input { "{\"other\":1}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1,}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1,,\"score\":2}" } output { false 0u64 0f64 false }
-- input { "{\"id\":}" } output { false 0u64 0f64 false }
-- input { "{\"id\"::1}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1 \"score\":2}" } output { false 0u64 0f64 false }
-- input { "{\"id\":1" } output { false 0u64 0f64 false }
-- input { "{\"id\":[1,2]}" } output { false 0u64 0f64 false }
-- input { "{\"score\":{\"id\":1}}" } output { false 0u64 0f64 false }
