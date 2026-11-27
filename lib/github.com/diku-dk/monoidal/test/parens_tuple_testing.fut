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

-- Independent sequential interpreter for complete inputs, plus a few cuts.
module Check (R:parens_regions with elem=M.t) = {
  module P = monoidal.Parens.Make X M R D
  def check (xs:[]u8) =
    let n=length xs
    let (stack,_) = loop (stack,level)=(replicate (n+1) M.ne,0i64)
      for c in xs do
        if c=='(' then (stack,level+1)
        else if c==')' then
          if level==0 then (stack,level)
          else let v=M.gen (#Nested (M.obs stack[level]))
               in (stack with [level-1]=M.op stack[level-1] v with [level]=M.ne,level-1)
        else (stack with [level]=M.op stack[level] (M.gen (#Raw c)),level)
    let parts=map (\c -> P.gen (if c=='(' || c==')' then #Del c else #E c)) xs
    let cuts=[(0,0),(0,n),(n,n),(n/3,2*n/3)]
    let observations=map (\(i,j) ->
      let pieces=map (\(a,b) -> reduce P.op P.ne parts[a:b]) [(0,i),(i,j),(j,n)]
      in map (\right ->
        let h=loop acc=P.ne for step<2 do
          let (a,b)=if right then
              if step==0 then (pieces[1],pieces[2]) else (pieces[0],acc)
            else if step==0 then (pieces[0],pieces[1]) else (acc,pieces[2])
          in P.op a b
        in P.obs h == M.obs stack[0]) [false,true]) cuts
    in all (all id) observations
}
