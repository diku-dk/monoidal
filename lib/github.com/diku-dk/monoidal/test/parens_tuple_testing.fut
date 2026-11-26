-- | ignore

import "../monoidal"
module M = {
 type t = (i64,i64)
 type i = nest u8 t
 type o = t
 def ne : t = (1,0)
 def op ((a,b):t) ((c,d):t) : t = ((a*c)%101,(a*d+b)%101)
 def gen (x:i) : t = match x
   case #Raw c -> if c=='a' then (2,1) else (3,4)
   case #Nested (a,b) -> ((a+1)%101,b)
 def obs (x:t) = x
}
module R0 = monoidal.Parens.Zero {type t=M.t}
module R1 = monoidal.Parens.Succ R0
module R2 = monoidal.Parens.Succ R1
module R3 = monoidal.Parens.Succ R2
module R4 = monoidal.Parens.Succ R3
module R5 = monoidal.Parens.Succ R4
module X = {type raw=u8 type value=M.t}
module D = {def left (c:u8)=c=='(' def right (c:u8)=c==')'}
def token (x:i64) : del u8 = match x
 case 0 -> #E 'a'
 case 1 -> #E 'b'
 case 2 -> #Del '('
 case 3 -> #Del ')'
 case _ -> #Del '?'
