import "../monoidal"
open monoidal
module Check (Y:integral) = {
  module M = nat_try Y
  def parse (xs:[]u8) : (bool,Y.t) =
    match M.obs (reduce M.op M.ne (map M.gen xs))
    case #some v -> (true,v)
    case _ -> (false,Y.i64 0)
  def laws (xs:[]u8) : bool =
    let eq ((a,b):M.t) ((c,d):M.t) = Y.(a == c && b == d)
    let parts = map M.gen xs
    let fold ys = reduce M.op M.ne ys
    let expected = fold parts
    in reduce (&&) true (map (\i ->
      reduce (&&) true (map (\j ->
        let a = fold parts[:i]
        let b = fold parts[i:j]
        let c = fold parts[j:]
        let l = M.op (M.op a b) c
        let r = M.op a (M.op b c)
        in eq l expected && eq r expected &&
           eq (M.op M.ne l) l && eq (M.op r M.ne) r)
        (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))
}
module U64 = Check u64
module U8 = Check u8
module I8 = Check i8
entry parse = U64.parse
entry parse_u8 = U8.parse
entry parse_i8 = I8.parse
entry laws (xs:[]u8) = U64.laws xs && U8.laws xs && I8.laws xs
entry zeros (n:i64) = U64.parse (replicate n '0')
entry zero_laws (n:i64) = U64.laws (replicate n '0')

-- ==
-- entry: parse
-- input { "" } output { false 0u64 }
-- input { "0" } output { true 0u64 }
-- input { "0005" } output { true 5u64 }
-- input { "123456789012345678" } output { true 123456789012345678u64 }
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { true 0u64 }
-- input { "18446744073709551621" } output { true 5u64 }
-- input { "-0" } output { false 0u64 }
-- input { "-5" } output { false 0u64 }
-- input { "+5" } output { false 0u64 }
-- input { "5.0" } output { false 0u64 }
-- input { " 5" } output { false 0u64 }
-- input { "5 " } output { false 0u64 }
-- input { "12x34" } output { false 0u64 }
-- input { [0u8] } output { false 0u64 }

-- ==
-- entry: parse_u8
-- input { "255" } output { true 255u8 }
-- input { "256" } output { true 0u8 }
-- input { "0000000" } output { true 0u8 }
-- input { "00000000" } output { false 0u8 }
-- input { "12345678" } output { false 0u8 }

-- ==
-- entry: parse_i8
-- input { "127" } output { true 127i8 }
-- input { "128" } output { true -128i8 }
-- input { "-1" } output { false 0i8 }
-- input { "00000000" } output { false 0i8 }

-- ==
-- entry: zeros
-- input { 63i64 } output { true 0u64 }
-- input { 64i64 } output { false 0u64 }
-- input { 65i64 } output { false 0u64 }

-- ==
-- entry: laws
-- input { "" } output { true }
-- input { "0" } output { true }
-- input { "123456789" } output { true }
-- input { "18446744073709551615" } output { true }
-- input { "18446744073709551616" } output { true }
-- input { "12x34" } output { true }
-- input { "-0" } output { true }

-- ==
-- entry: zero_laws
-- input { 63i64 } output { true }
-- input { 64i64 } output { true }
-- input { 65i64 } output { true }
