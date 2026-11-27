import "monoidal_json_testing"
entry main = array_count

-- ==
-- entry: main
-- input { "[]" } output { true 0i64 }
-- input { "[{\"a\":1,\"b\":2.5},{\"b\":0.25}]" } output { true 2i64 }
-- input { "[{\"a\":1}]" } output { true 1i64 }
-- input { "[{\"a\":1},{\"b\":bad}]" } output { false 0i64 }
-- input { "[{\"a\":1}{\"a\":2}]" } output { false 0i64 }
-- input { "[{\"a\":1},]" } output { false 0i64 }
-- input { "[{\"a\":1},,{\"a\":2}]" } output { false 0i64 }
-- input { "[{\"a\":1]" } output { false 0i64 }
-- input { "[[{\"a\":1}]]" } output { false 0i64 }
-- input { "[{\"a\":{\"a\":1}}]" } output { false 0i64 }
