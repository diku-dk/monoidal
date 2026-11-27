import "json_primitives_testing"
entry main = boolean

-- ==
-- entry: main
-- input { "true" } output { true true }
-- input { "false" } output { true false }
-- input { "True" } output { false false }
-- input { "FALSE" } output { false false }
-- input { "tru" } output { false false }
-- input { "falsex" } output { false false }
-- input { "truefalse" } output { false false }
-- input { "\"true\"" } output { false false }
-- input { " true" } output { false false }
-- input { "" } output { false false }
