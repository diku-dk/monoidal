import "../monoidal"
import "../monoidal_json"
open monoidal
open monoidal_json
module Int = int_try i64

module Check (Y:integral) = {
  module M = int_try Y
  def parse (xs:[]u8) : (bool,Y.t) =
    match M.obs (reduce M.op M.ne (map M.gen xs))
    case #some v -> (true,v)
    case _ -> (false,Y.i64 0)
  def laws (xs:[]u8) : bool =
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
        in l == expected && r == expected &&
           M.op M.ne l == l && M.op r M.ne == r)
        (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))
}
module I8 = Check i8
module I16 = Check i16
module I32 = Check i32
module U8 = Check u8
module U16 = Check u16
module U32 = Check u32
module U64 = Check u64
entry parse_i8 = I8.parse
entry parse_i16 = I16.parse
entry parse_i32 = I32.parse
entry parse_u8 = U8.parse
entry parse_u16 = U16.parse
entry parse_u32 = U32.parse
entry parse_u64 = U64.parse
entry unsigned_laws = U64.laws

entry integer (xs:[]u8) : (bool,i64) =
  match Int.obs (reduce Int.op Int.ne (map Int.gen xs))
  case #some v -> (true,v)
  case _ -> (false,0)

entry integer_laws (xs:[]u8) : bool =
  let parts = map Int.gen xs
  let fold ys = reduce Int.op Int.ne ys
  let expected = fold parts
  in reduce (&&) true (map (\i ->
    reduce (&&) true (map (\j ->
      let a = fold parts[:i]
      let b = fold parts[i:j]
      let c = fold parts[j:]
      let l = Int.op (Int.op a b) c
      let r = Int.op a (Int.op b c)
      in l == expected && r == expected &&
         Int.op Int.ne l == l && Int.op r Int.ne == r)
      (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))

-- Different names, types, defaults, and field order: not hardwired to JSON.
module X = field {type t=f64} (float_try f64) {
  def key = Key.pack "x"
  def default = 1.5f64
}
module Y = field {type t=i64} (int_try i64) {
  def key = Key.pack "y"
  def default = 9i64
}
module R = monoidal_json.Record.Make
  (monoidal_json.Record.Succ X
    (monoidal_json.Record.Succ Y monoidal_json.Record.Zero))
entry record (xs:[]u8) : (bool,f64,i64) =
  match R.obs (reduce R.op R.ne (map R.gen xs))
  case #some (a,(b,())) -> (true,a,b)
  case _ -> (false,0,0)

module S = separated (sum i64) {def delimiter:u8=';'}
def symbol (c:u8) : S.i =
  if c >= '0' && c <= '9' then #Nested (#some (i64.u8 (c-'0')))
  else #Raw c
module Bytes = with_gen S {type i=u8 def gen = symbol}
module Wrapped = enclosed {type t=i64} Bytes {def left:u8='(' def right:u8=')'}
entry separated_list (xs:[]u8) : (bool,i64) =
  match Wrapped.obs (reduce Wrapped.op Wrapped.ne (map Wrapped.gen xs))
  case #some v -> (true,v)
  case _ -> (false,0)

-- Configuration errors are distinct from malformed input.
module Same = monoidal_json.Record.Make
  (monoidal_json.Record.Succ Y
    (monoidal_json.Record.Succ Y monoidal_json.Record.Zero))
entry duplicate_keys (xs:[]u8) : bool =
  match Same.obs (reduce Same.op Same.ne (map Same.gen xs))
  case #some _ -> true case _ -> false

-- ==
-- entry: integer
-- input { "0" } output { true 0i64 }
-- input { "-0" } output { true 0i64 }
-- input { "-123456789012345678" } output { true -123456789012345678i64 }
-- input { "9223372036854775807" } output { true 9223372036854775807i64 }
-- input { "-9223372036854775808" } output { true -9223372036854775808i64 }
-- input { "9223372036854775808" } output { false 0i64 }
-- input { "-9223372036854775809" } output { false 0i64 }
-- input { "9999999999999999999" } output { false 0i64 }
-- input { "00000000000000000000" } output { true 0i64 }
-- input { "000000000000000000000" } output { false 0i64 }
-- input { "" } output { false 0i64 }
-- input { "-" } output { false 0i64 }
-- input { "--1" } output { false 0i64 }
-- input { "1-" } output { false 0i64 }
-- input { "+1" } output { false 0i64 }
-- input { "1.0" } output { false 0i64 }

-- ==
-- entry: integer_laws
-- input { "-9223372036854775808" } output { true }
-- input { "9223372036854775808" } output { true }
-- input { "00000000000000000000" } output { true }
-- input { "--1" } output { true }
-- input { "1-" } output { true }
-- input { "" } output { true }

-- ==
-- entry: record
-- input { "{\"y\":-42,\"x\":5.25}" } output { true 5.25f64 -42i64 }
-- input { "{\"x\":2.5}" } output { true 2.5f64 9i64 }
-- input { "{\"y\":0}" } output { true 1.5f64 0i64 }
-- input { "{\"x\":2,\"x\":3,\"y\":7,\"y\":8}" } output { true 3f64 8i64 }
-- input { "{\"y\":1.5}" } output { false 0f64 0i64 }
-- input { "{\"x\":5,,\"y\":2}" } output { false 0f64 0i64 }
-- input { "{\"z\":5}" } output { false 0f64 0i64 }

-- ==
-- entry: separated_list
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

-- ==
-- entry: duplicate_keys
-- input { "{\"y\":5}" } error: .*

-- ==
-- entry: parse_i8
-- input { "127" } output { true 127i8 }
-- input { "128" } output { false 0i8 }
-- input { "-128" } output { true -128i8 }
-- input { "-129" } output { false 0i8 }
-- input { "-0" } output { true 0i8 }

-- ==
-- entry: parse_i16
-- input { "32767" } output { true 32767i16 }
-- input { "32768" } output { false 0i16 }
-- input { "-32768" } output { true -32768i16 }
-- input { "-32769" } output { false 0i16 }

-- ==
-- entry: parse_i32
-- input { "2147483647" } output { true 2147483647i32 }
-- input { "2147483648" } output { false 0i32 }
-- input { "-2147483648" } output { true -2147483648i32 }
-- input { "-2147483649" } output { false 0i32 }

-- ==
-- entry: parse_u8
-- input { "255" } output { true 255u8 }
-- input { "256" } output { false 0u8 }
-- input { "-1" } output { false 0u8 }
-- input { "-0" } output { false 0u8 }

-- ==
-- entry: parse_u16
-- input { "65535" } output { true 65535u16 }
-- input { "65536" } output { false 0u16 }
-- input { "-0" } output { false 0u16 }

-- ==
-- entry: parse_u32
-- input { "4294967295" } output { true 4294967295u32 }
-- input { "4294967296" } output { false 0u32 }
-- input { "-0" } output { false 0u32 }

-- ==
-- entry: parse_u64
-- input { "18446744073709551615" } output { true 18446744073709551615u64 }
-- input { "18446744073709551616" } output { false 0u64 }
-- input { "99999999999999999999" } output { false 0u64 }
-- input { "10000000000000000000" } output { true 10000000000000000000u64 }
-- input { "00000000000000000001" } output { true 1u64 }
-- input { "000000000000000000001" } output { false 0u64 }
-- input { "-0" } output { false 0u64 }
-- input { "-1" } output { false 0u64 }
-- input { "" } output { false 0u64 }

-- ==
-- entry: unsigned_laws
-- input { "18446744073709551615" } output { true }
-- input { "18446744073709551616" } output { true }
-- input { "99999999999999999999" } output { true }
-- input { "00000000000000000001" } output { true }
-- input { "000000000000000000001" } output { true }
-- input { "-0" } output { true }
