import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests total_float_example.M

module Float = total_float_example.M

def value (s:Float.t) = match Float.obs s
  case #some x -> x
  case #none -> -999999f64

entry test_float_try_splits (xs:[]u8) : bool = Check.splits total_float_example.same xs

-- Exercise both trees across a decimal point and their continuation.
entry test_float_fragments (xs:[]u8) (ys:[]u8) (zs:[]u8) (ws:[]u8) : [4]f64 =
  let a = length xs
  let b = a+length ys
  let c = b+length zs
  let d = c+length ws
  let pieces = Check.folds (map Float.gen (xs++ys++zs++ws)) [(0,a),(a,b),(b,c),(c,d)]
  in map (\which ->
    let result = loop acc=Float.ne for step < 3 do
      if step == 2 && which < 2 then acc
      else
        let (l,r) = if step == 2 then (acc,pieces[3])
          else if which % 2 == 1 then
            if step == 0 then (pieces[1],pieces[2]) else (pieces[0],acc)
          else if step == 0 then (pieces[0],pieces[1]) else (acc,pieces[2])
        in Float.op l r
    in value result) (iota 4)

-- ==
-- entry: test_float_try_splits
-- input { "12.34" }
-- output { true }
-- input { "-.5" }
-- output { true }
-- input { "1.2.3" }
-- output { true }
-- input { "1-2" }
-- output { true }


-- ==
-- entry: test_float_fragments
-- input { "1" "." "23" "45" }
-- output { [1.23f64, 1.23f64, 1.2345f64, 1.2345f64] }
-- input { "12" "." "345" "67" }
-- output { [12.345f64, 12.345f64, 12.34567f64, 12.34567f64] }
-- input { "-" "." "23" "45" }
-- output { [-0.23f64, -0.23f64, -0.2345f64, -0.2345f64] }
-- input { "-12" "." "03" "04" }
-- output { [-12.03f64, -12.03f64, -12.0304f64, -12.0304f64] }
-- input { "" "." "23" "45" }
-- output { [0.23f64, 0.23f64, 0.2345f64, 0.2345f64] }
