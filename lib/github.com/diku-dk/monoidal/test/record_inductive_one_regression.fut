import "record_inductive_testing"
entry main = one

-- ==
-- entry: main
-- input { "{\"id\":12}" } output { true 12u64 }
-- input { "{\"score\":2}" } output { false 0u64 }
-- input { "{}" } output { false 0u64 }
