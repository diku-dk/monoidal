import "../monoidal"
module M = monoidal

-- Exact, order-sensitive summaries expose missing, duplicated, or reordered bytes.
module Bytes = {
  type t = (u64,u64,i64)
  type i = u8
  type o = opt (u64,i64)
  def ne : t = (0,1,0)
  def gen (c:i) : t = (u64.u8 c,257,1)
  def op ((a,p,n):t) ((b,q,m):t) : t = (a*q+b,p*q,n+m)
  def obs ((a,_,n):t) : o = #some (a,n)
}
module Check (D:{val left:u8 val right:u8}) = {
  module P = M.enclosed {type t=(u64,i64)} Bytes D
  def check (xs:[]u8) =
    let parts = map P.gen xs
    let fold ys = reduce P.op P.ne ys
    let expected = if length xs >= 2 && xs[0] == D.left && xs[length xs-1] == D.right
      then Bytes.obs (reduce Bytes.op Bytes.ne (map Bytes.gen xs[1:length xs-1]))
      else #none
    in P.obs (fold parts) == expected &&
       reduce (&&) true (map (\i ->
         reduce (&&) true (map (\j ->
           let a = fold parts[:i]
           let b = fold parts[i:j]
           let c = fold parts[j:]
           let l = P.op (P.op a b) c
           let r = P.op a (P.op b c)
           in l == r && P.obs l == expected &&
              P.op P.ne l == l && P.op r P.ne == r)
           (map (+i) (iota (length xs-i+1))))) (iota (length xs+1)))
}
module Brackets = Check {def left:u8='[' def right:u8=']'}
module Quotes = Check {def left:u8='"' def right:u8='"'}
entry brackets (xs:[]u8) = Brackets.check xs
entry quotes (xs:[]u8) = Quotes.check xs

-- ==
-- entry: brackets
-- input { "" } output { true }
-- input { "[" } output { true }
-- input { "[]" } output { true }
-- input { "[a]" } output { true }
-- input { "[abcdef]" } output { true }
-- input { "[12,34,56]" } output { true }
-- input { "[abc" } output { true }
-- input { "abc]" } output { true }
-- input { "[abc)" } output { true }
-- input { "[[abc]]" } output { true }

-- ==
-- entry: quotes
-- input { "" } output { true }
-- input { "\"" } output { true }
-- input { "\"\"" } output { true }
-- input { "\"abc\"" } output { true }
-- input { "\"abcdef\"" } output { true }
-- input { "\"abc" } output { true }
