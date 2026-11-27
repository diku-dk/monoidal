-- | ignore

import "../monoidal"
module D = monoidal.decimal_try f64
module A = monoidal.decimal f64
def all f xs = reduce (&&) true (map f xs)
def fold xs = loop s=D.ne for c in xs do D.op s (D.gen c)
def lawful xs =
  let h = fold xs
  in D.op D.ne h == h && D.op h D.ne == h &&
     reduce D.op D.ne (map D.gen xs) == h &&
     all (\i -> all (\j ->
       let a=fold xs[:i]
       let b=fold xs[i:i+j]
       let c=fold xs[i+j:]
       in D.op (D.op a b) c == h && D.op a (D.op b c) == h)
       (iota (length xs-i+1))) (iota (length xs+1))
def parse (xs:[]u8) = match D.obs (fold xs)
  case #some v -> (true,v)
  case #none -> (false,0f64)
def splits (xs:[]u8) = lawful xs
def signed_zero (_:bool) =
  let v=A.obs (reduce A.op A.ne (map A.gen "-0.000"))
  in 1f64/v < 0
