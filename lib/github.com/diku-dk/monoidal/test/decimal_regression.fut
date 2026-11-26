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
entry parse (xs:[]u8) = match D.obs (fold xs)
  case #some v -> (true,v)
  case #none -> (false,0f64)
entry splits (xs:[]u8) = lawful xs
entry exhaustive (_:bool) =
  let alphabet = ['0','7','.','-','x']
  in all (\n ->
    let count = loop p=1i64 for _i<n do p*5
    in all (\code ->
      let (_,xs) = loop (k,xs)=(code,replicate n '0') for i<n do
        (k/5,xs with [i]=alphabet[k%5])
      in lawful xs) (iota count)) (iota 6)
entry signed_zero (_:bool) =
  let v=A.obs (reduce A.op A.ne (map A.gen "-0.000"))
  in 1f64/v < 0

-- ==
-- entry: exhaustive signed_zero
-- input { true }
-- output { true }

-- ==
-- entry: parse
-- input { "-12.034" }
-- output { true -12.034f64 }
-- input { "0012.500" }
-- output { true 12.5f64 }
-- input { "0" }
-- output { true 0f64 }
-- input { "-123456789012345678" }
-- output { true -123456789012345678f64 }
-- input { "0.12345678901234567" }
-- output { true 0.12345678901234567f64 }
-- input { "999999999999999999" }
-- output { true 999999999999999999f64 }
-- input { "0000000000000000000" }
-- output { false 0f64 }
-- input { "1234567890123456789" }
-- output { false 0f64 }
-- input { "" }
-- output { false 0f64 }
-- input { "-" }
-- output { false 0f64 }
-- input { "-." }
-- output { false 0f64 }
-- input { ".5" }
-- output { false 0f64 }
-- input { "5." }
-- output { false 0f64 }
-- input { "1.2.3" }
-- output { false 0f64 }
-- input { "1-2" }
-- output { false 0f64 }
-- input { "--12" }
-- output { false 0f64 }
-- input { "+12" }
-- output { false 0f64 }
-- input { "1e2" }
-- output { false 0f64 }
-- input { " 12" }
-- output { false 0f64 }

-- ==
-- entry: splits
-- input { "-123456789012345.678" }
-- output { true }
-- input { "1234567890123456789" }
-- output { true }
-- input { "-0000000000000000000" }
-- output { true }
-- input { "123456789.012345678." }
-- output { true }
