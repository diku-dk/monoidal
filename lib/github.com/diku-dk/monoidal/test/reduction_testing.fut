-- Shared law checks: batching fragment folds and looping over tree steps
-- avoids duplicating a large monoid operation at each syntactic call site.
import "../monoidal"

module ReductionTests (M:monoid with i=u8) = {
  def folds (parts:[]M.t) (ranges:[](i64,i64)) =
    map (\(lo,hi) -> reduce M.op M.ne parts[lo:hi]) ranges

  def splits (eq:M.o -> M.o -> bool) (xs:[]u8) =
    let n = length xs
    let parts = map M.gen xs
    in reduce (&&) true (map (\i ->
      let pieces = folds parts [(0,n),(0,i),(i,n)]
      let results = map M.obs [pieces[0],M.op pieces[1] pieces[2]]
      in eq results[0] results[1]) [0,n/2,n])

  def associations (eq:M.o -> M.o -> bool) (xs:[]u8) =
    let n=length xs
    let parts=map M.gen xs
    let cuts=[(0,0),(0,n),(n,n),(n/3,2*n/3)]
    in all (\(i,j) ->
      let pieces=folds parts [(0,n),(0,i),(i,j),(j,n)]
      let expected=M.obs pieces[0]
      in all (\right ->
        let result=loop acc=M.ne for step<2 do
          let (a,b)=if right then
              if step==0 then (pieces[2],pieces[3]) else (pieces[1],acc)
            else if step==0 then (pieces[1],pieces[2]) else (acc,pieces[3])
          in M.op a b
        in eq expected (M.obs result)) [false,true]) cuts
}
