import "keys_testing"
entry main (n:i64) = constant (replicate n 'a')
-- ==
-- input { 254i64 } output { true }
-- input { 255i64 } output { true }
-- input { 4096i64 } output { true }
