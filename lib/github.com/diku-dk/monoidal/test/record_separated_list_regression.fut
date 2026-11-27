import "record_testing"
entry main = separated_list

-- ==
-- entry: main
-- input { "()" } output { true 0i64 }
-- input { "(1;2;3)" } output { true 6i64 }
-- input { "(12)" } output { false 0i64 }
-- input { "(;1)" } output { false 0i64 }
-- input { "(1;)" } output { false 0i64 }
-- input { "(1;;2)" } output { false 0i64 }
-- input { "(1,2)" } output { false 0i64 }
-- input { "(1;2]" } output { false 0i64 }
-- input { "(" } output { false 0i64 }
-- input { "" } output { false 0i64 }
