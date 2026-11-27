import "json_primitives_testing"
entry main = boolean_splits

-- ==
-- entry: main
-- input { "true" } output { true }
-- input { "false" } output { true }
-- input { "truefalse" } output { true }
-- input { "" } output { true }
