import "../monoidal"
module M = monoidal
module Left = M.sum i64
module Right = M.count {type i=i64}
module Pair = M.delim_prod Left Right
-- Small summaries isolate delim_prod's laws from numeric/key parsing.
def fold (xs:[]u8) = reduce Pair.op Pair.ne
  (map (\c -> Pair.gen (if c % 3 == 0 then #Del ':' else #E (i64.u8 c))) xs)
#[prop(size(8))]
entry main ((xs,ys,zs):([]u8,[]u8,[]u8)) =
  let pieces=map (\(lo,hi) -> fold (xs++ys++zs)[lo:hi])
    [(0,length xs),(length xs,length xs+length ys),(length xs+length ys,length xs+length ys+length zs)]
  in Pair.obs (Pair.op (Pair.op pieces[0] pieces[1]) pieces[2]) ==
     Pair.obs (Pair.op pieces[0] (Pair.op pieces[1] pieces[2]))
-- ==
-- property: main
