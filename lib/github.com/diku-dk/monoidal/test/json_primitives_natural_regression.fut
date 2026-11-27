import "json_primitives_testing"
entry main = natural

-- ==
-- entry: main
-- input { "0" } output { true 0u64 }
-- input { "0005" } output { true 5u64 }
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { true 0u64 }
-- input { "-0" } output { false 0u64 }
-- input { "1.0" } output { false 0u64 }
-- input { "" } output { false 0u64 }
