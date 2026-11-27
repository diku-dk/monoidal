-- Former length boundaries now succeed; long strings also wrap u32 arithmetic.
import "keys_hash_testing"
entry main (a:i64) (b:i64) (c:i64) =
  laws (replicate a 'a') (replicate b 'b') (replicate c 'c')
-- ==
-- input { 0i64 0i64 0i64 } output { true }
-- input { 0i64 254i64 0i64 } output { true }
-- input { 253i64 1i64 0i64 } output { true }
-- input { 127i64 0i64 127i64 } output { true }
-- input { 85i64 85i64 84i64 } output { true }
-- input { 254i64 1i64 0i64 } output { true }
-- input { 0i64 1i64 254i64 } output { true }
-- input { 85i64 85i64 85i64 } output { true }
-- input { 255i64 0i64 0i64 } output { true }
-- input { 0i64 0i64 256i64 } output { true }
-- input { 254i64 254i64 254i64 } output { true }
-- input { 1024i64 1024i64 1024i64 } output { true }
