import "record_testing"
entry main = parse_i32

-- ==
-- entry: main
-- input { "2147483647" } output { true 2147483647i32 }
-- input { "2147483648" } output { false 0i32 }
-- input { "-2147483648" } output { true -2147483648i32 }
-- input { "-2147483649" } output { false 0i32 }
