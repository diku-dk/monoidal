import "../json_ex"
entry main = key_matches

-- ==
-- entry: main
-- input { "\"id\"" "id" } output { true }
-- input { "\"score\"" "score" } output { true }
-- input { "\"abcdefg\"" "abcdefg" } output { true }
-- input { "\"a_1\"" "a_1" } output { true }
-- input { "id" "id" } output { false }
-- input { "\"id" "id" } output { false }
-- input { "id\"" "id" } output { false }
-- input { "\"i\"d\"" "id" } output { false }
-- input { "\"i\\d\"" "id" } output { false }
-- input { "\"id,score\"" "id" } output { false }
-- input { "\"id:score\"" "id" } output { false }
-- input { "\"\"" "" } output { false }
-- input { "\"abcdefgh\"" "id" } output { false }
-- input { "\"i\td\"" "id" } output { false }
