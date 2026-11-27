-- | ignore

import "../monoidal"
open monoidal
module Number = decimal f64
module Sum = sum f64
module Mul = mul f64
module Nested = nestable Number
module Groups = chunk Sum (optone f64) {def del_ign (c:u8) = c == '+'}
module Items = chunk Mul Groups {def del_ign (c:u8) = c == '*'}
module O = chunk Nested Items {def del_ign (_:u8) = false}
module Outer = with_gen O {
 type i = nest (del u8) f64
 def gen (x:i) : O.i = match x
 case #Raw (#E c) -> #E (#Raw c)
 case #Raw (#Del c) -> #Del c
 case #Nested v -> #E (#Nested v)
}

module R0 = Parens.Zero {type t=Outer.t}
module R1 = Parens.Succ R0
module R2 = Parens.Succ R1
module P = Parens.Make {type raw=del u8 type value=f64} Outer R2 {
 def left (c:u8) = c=='('
 def right (c:u8) = c==')'
}
entry main (xs:[]u8) =
 let tokens=map (\c -> if c=='(' || c==')' then #Del c
   else if c=='+' || c=='*' then #E (#Del c) else #E (#E c)) xs
 in P.obs (reduce P.op P.ne (map P.gen tokens))
-- ==
-- input { "12.5*(2.0+(3.0*0.5))+78" }
-- output { 121.75f64 }
-- input { "(12.25+3.75)*(20.5+(2.5*4.0))" }
-- output { 488.0f64 }
-- input { "12.5*((3.0+1.0))+78.0" }
-- output { 128.0f64 }
-- input { "(((1.0)))" } error: .*
-- input { "(1.0" } error: .*
-- input { "1.0)" } error: .*
-- input { ")1.0(" } error: .*
-- input { "(1..0)" } error: .*
