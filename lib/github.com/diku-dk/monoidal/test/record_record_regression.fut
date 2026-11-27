import "record_testing"
entry main = record

-- ==
-- entry: main
-- input { "{\"y\":-42,\"x\":5.25}" } output { true 5.25f64 -42i64 }
-- input { "{\"x\":2.5}" } output { true 2.5f64 9i64 }
-- input { "{\"y\":0}" } output { true 1.5f64 0i64 }
-- input { "{\"x\":2,\"x\":3,\"y\":7,\"y\":8}" } output { true 3f64 8i64 }
-- input { "{\"y\":1.5}" } output { false 0f64 0i64 }
-- input { "{\"x\":5,,\"y\":2}" } output { false 0f64 0i64 }
-- input { "{\"z\":5}" } output { false 0f64 0i64 }
