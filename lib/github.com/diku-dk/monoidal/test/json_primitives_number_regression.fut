import "json_primitives_testing"
entry main = number

-- ==
-- entry: main
-- input { "-12.75" } output { true -12.75f64 }
-- input { "005.25" } output { true 5.25f64 }
-- input { "1e2" } output { false 0f64 }
-- input { ".5" } output { false 0f64 }
-- input { "5." } output { false 0f64 }
-- input { "0000000000000000000" } output { false 0f64 }
-- input { "" } output { false 0f64 }
