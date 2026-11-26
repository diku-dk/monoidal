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
      in eq results[0] results[1]) (iota (n+1)))

  def associations (eq:M.o -> M.o -> bool) (xs:[]u8) =
    let n = length xs
    let parts = map M.gen xs
    in reduce (&&) true (map (\i ->
      reduce (&&) true (map (\j ->
        let pieces = folds parts [(0,i),(i,j),(j,n)]
        let results = map (\right ->
          let result = loop acc=M.ne for step < 2 do
            let (a,b) = if right then
                if step == 0 then (pieces[1],pieces[2]) else (pieces[0],acc)
              else if step == 0 then (pieces[0],pieces[1]) else (acc,pieces[2])
            in M.op a b
          in M.obs result) [false,true]
        in eq results[0] results[1]) (map (+i) (iota (n-i+1))))) (iota (n+1)))
}
