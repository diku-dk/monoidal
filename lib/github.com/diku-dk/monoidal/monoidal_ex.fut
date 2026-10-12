import "monoidal"

-- ---------------------------------------------------------------------
-- Total floating-point parser
-- ---------------------------------------------------------------------

module total_float_example = {
  open monoidal
  module M = float_try f64

  def parse [n] (xs:[n]u8) : opt f64 =
    reduce M.op M.ne (map M.gen xs) |> M.obs

  def parse_pair [n] (xs:[n]u8) : (bool,f64) =
    match parse xs
    case #some x -> (true,x)
    case #none -> (false,0)

  def same (x:opt f64) (y:opt f64) : bool =
    match (x,y)
    case (#some x, #some y) -> x == y
    case (#none, #none) -> true
    case _ -> false

  def split_consistent [n] (xs:[n]u8) : bool =
    let expected = parse xs
    let parts = map M.gen xs
    let agrees (i:i64) =
      M.obs (M.op (reduce M.op M.ne parts[:i])
                  (reduce M.op M.ne parts[i:]))
      |> same expected
    in reduce (&&) true (map agrees (iota (n+1)))
}

entry test_float_try [n] (xs:[n]u8) : (bool,f64) =
  total_float_example.parse_pair xs

entry test_float_try_splits [n] (xs:[n]u8) : bool =
  total_float_example.split_consistent xs

-- Force both reduction trees across a decimal point, then append digits
-- to check the fractional scale retained in each summary.
entry test_float_fragments [a][b][c][d]
    (xs:[a]u8) (ys:[b]u8) (zs:[c]u8) (ws:[d]u8) : [4]f64 =
  let summarise xs = reduce total_float_example.M.op
    total_float_example.M.ne (map total_float_example.M.gen xs)
  let op = total_float_example.M.op
  let value s = match total_float_example.M.obs s
                case #some x -> x
                case #none -> -999999f64
  let x = summarise xs
  let y = summarise ys
  let z = summarise zs
  let w = summarise ws
  let left = op (op x y) z
  let right = op x (op y z)
  in map value [left, right, op left w, op right w]

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

module or_example = {
  open monoidal
  module decimal = float_try f64
  module alternate_decimal = with_gen (float_try f64) {
    type i = u8
    def gen (c:i) =
      if c == ',' then '.'
      else if c == '1' then '9'
      else c
  }
  module M = or { type t = f64 } decimal alternate_decimal

  def parse [n] (xs:[n]u8) : opt f64 =
    reduce M.op M.ne (map M.gen xs) |> M.obs

  def parse_pair [n] (xs:[n]u8) : (bool,f64) =
    match parse xs
    case #some x -> (true,x)
    case #none -> (false,0)

  def same (x:opt f64) (y:opt f64) : bool =
    match (x,y)
    case (#some x, #some y) -> x == y
    case (#none, #none) -> true
    case _ -> false

  def split_consistent [n] (xs:[n]u8) : bool =
    let expected = parse xs
    let parts = map M.gen xs
    let agrees (i:i64) =
      M.obs (M.op (reduce M.op M.ne parts[:i])
                  (reduce M.op M.ne parts[i:]))
      |> same expected
    in reduce (&&) true (map agrees (iota (n+1)))
}

entry test_or [n] (xs:[n]u8) : (bool,f64) =
  or_example.parse_pair xs

entry test_or_splits [n] (xs:[n]u8) : bool =
  or_example.split_consistent xs

-- Tests of or.  The alternate branch accepts comma as a decimal separator
-- and maps 1 to 9, making left-biased choice observable when both succeed.
-- entry: test_or
-- input { "12.34" }
-- output { true 12.34f64 }
-- input { "12,34" }
-- output { true 92.34f64 }
-- input { "1234" }
-- output { true 1234f64 }
-- input { "1.2.3" }
-- output { false 0f64 }
-- input { "not-a-number" }
-- output { false 0f64 }

-- entry: test_or_splits
-- input { "12.34" }
-- output { true }
-- input { "12,34" }
-- output { true }
-- input { "1.2.3" }
-- output { true }

-- Tests of float_try
-- ==
-- entry: test_float_try
-- input { "12.34" }
-- output { true 12.34f64 }
-- input { "-.5" }
-- output { true -0.5f64 }
-- input { "-." }
-- output { true 0f64 }
-- input { "" }
-- output { false 0f64 }
-- input { "." }
-- output { false 0f64 }
-- input { "-" }
-- output { false 0f64 }
-- input { "1.2.3" }
-- output { false 0f64 }
-- input { "1-2" }
-- output { false 0f64 }
-- input { "number" }
-- output { false 0f64 }

-- The success or failure result is independent of the reduction split.
-- entry: test_float_try_splits
-- input { "12.34" }
-- output { true }
-- input { "-.5" }
-- output { true }
-- input { "1.2.3" }
-- output { true }
-- input { "1-2" }
-- output { true }

-- ---------------------------------------------------------------------
-- Example computing the maximum of the sums of elements in a series of
-- grouped floats; the floats are separated by commas (,) and the groups
-- are separated by bars (|).
-- ---------------------------------------------------------------------

module max_sums : { val red [n] : [n]u8 -> f64 } = {

  open monoidal

  module groups = chunk (max f64) (optone f64) { def del_ign (c:u8) : bool = c == '|' }
  module items = chunk (sum f64) groups { def del_ign (c:u8) : bool = c == ',' }
  module M = chunk (float f64) items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : f64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}

entry test_max_sums [n] (xs: [n]u8) : f64 =
  max_sums.red xs

-- Tests of max_sums - inspired by advent of code 2022
-- ==
-- entry: test_max_sums
-- input { "34" }
-- output { 34f64 }
-- input { "34,234,23,23|23,2|22,3,2|122" }
-- output { 314f64 }
-- input { "34,234,23,23|23,2|22.01,3.4,300,2|122" }
-- output { 327.41f64 }
-- input { "34.8" }
-- output { 34.8f64 }
-- input { "34,234,-23,23,24|23,-2.23|22.01,68,3.4,-64,300,-4,2|122|5032.2,-5000.0" }
-- output { 327.41f64 }
-- input @ ex.txt
-- output { 36521f64 }

-- ---------------------------------------------------------------------
-- Example computing the maximum average of a series of grouped floats
-- ---------------------------------------------------------------------

module max_avgs : { val red [n] : [n]u8 -> f64 } = {
  open monoidal

  module avg (X:numeric) : monoid with i = X.t with o = X.t = {
    module Y = dup { type i = X.t }
	     (prod (sum X) (count { type i = X.t }))
    open Y
    type o = X.t
    def obs (t:t) : o =
      let (s,c) = Y.obs t
      in if c == 0 then X.i64 0 else s X./ (X.i64 c)
  }

  module groups = chunk (max f64) (optone f64) { def del_ign (c:u8) : bool = c == '|' }
  module items = chunk (avg f64) groups { def del_ign (c:u8) : bool = c == ',' }
  module M = chunk (float f64) items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : f64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}

entry test_max_avgs [n] (xs: [n]u8) : f64 =
  max_avgs.red xs

-- Tests of max_avgs
-- ==
-- entry: test_max_avgs
-- input { "34" }
-- output { 34f64 }
-- input { "3,5,4" }
-- output { 4f64 }
-- input { "3,5,4|10,12,11|100,200|7,8,9" }
-- output { 150f64 }
-- input @ ex.txt
-- output { 908.71f64 }

entry bench_max_avgs [n] (xs: [n]u8) : f64 =
  max_avgs.red xs

-- Bench of max_avgs
-- ==
-- entry: bench_max_avgs
-- notest input @ ex.txt
-- output { 908.71f64 }
-- notest input @ ../../../../util/ex50.txt
-- output { 866.25 }
-- notest input @ ../../../../util/ex100.txt
-- output { 989.5714285714286 }
-- notest input @ ../../../../util/ex200.txt
-- output { 1028.0 }
-- notest input @ ../../../../util/ex400.txt
-- output { 1225.25 }
-- notest input @ ../../../../util/ex800.txt
-- output { 1056.142857142857 }
-- notest input @ ../../../../util/ex1600.txt
-- output { 1092.5714285714287 }
-- notest input @ ../../../../util/ex3200.txt
-- output { 1100.75 }
-- notest input @ ../../../../util/ex6400.txt
-- output { 1070.4285714285713 }
-- notest input @ ../../../../util/ex12800.txt
-- output { 1208.0 }

-- ---------------------------------------------------------------------
-- Example computing the maximum count of a series of grouped nats
-- ---------------------------------------------------------------------

module max_counts : { val red [n] : [n]u8 -> i64 } = {
  open monoidal

  module groups = chunk (max i64) (optone i64) { def del_ign (c:u8) : bool = c == '|' }
  module items = chunk (count {type i = i64}) groups { def del_ign (c:u8) : bool = c == ',' }
  module M = chunk (nat i64) items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : i64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}

entry test_max_counts [n] (xs: [n]u8) : i64 =
  max_counts.red xs

-- Tests of max_counts
-- ==
-- entry: test_max_counts
-- input { "34" }
-- output { 1i64 }
-- input { "3,5,4" }
-- output { 3i64 }
-- input { "3,5,4|10,12,11|3,2,100,200|7,8,9" }
-- output { 4i64 }

-- ---------------------------------------------------------------------
-- Example computing the sum of those comma-separated integers that are
-- larger than 10.
-- ---------------------------------------------------------------------

module sum_greaterthan10 : { val red [n] : [n]u8 -> i64 } = {
  open monoidal

  module gt10 = filter (nat i64) { def pred (i : i64) = i > 10 }

  module items = chunk (sum i64) (optone i64) { def del_ign (c:u8) : bool = c == ',' }
  module M = chunk gt10 items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : i64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}

entry test_sum_greaterthan10 [n] (xs: [n]u8) : i64 =
  sum_greaterthan10.red xs

-- Tests of sum_greaterthan10
-- ==
-- entry: test_sum_greaterthan10
-- input { "3,5,4,12,10,11,3,2,100,200,7,8,9" }
-- output { 323i64 }

-- -------------------------------------
-- Example computing the sum of products
-- -------------------------------------

module sumofproducts : { val red [n] : [n]u8 -> f64 } = {

  open monoidal

  module groups = chunk (sum f64) (optone f64) { def del_ign (c:u8) : bool = c == '+' }
  module items = chunk (mul f64) groups { def del_ign (c:u8) : bool = c == '*' }
  module M = chunk (float f64) items { def del_ign (_ :u8) : bool = false }

  module T = with_gen M {
    type i = u8
    def gen (c:i) : M.i =
      if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E c else #Del c
  }

  def red [n] (xs:[n]u8) : f64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs
}

entry test_sumofproducts [n] (xs: [n]u8) : f64 =
  sumofproducts.red xs

-- Tests of sumofproducts
-- ==
-- entry: test_sumofproducts
-- input { "34" }
-- output { 34f64 }
-- input { "34*234*23*23+23*2+22*3*2+122" }
-- output { 4209024f64 }

-- ---------------------------------------------------------------------
-- Sum of products with one supported layer of parentheses
-- ---------------------------------------------------------------------

module parenthesised_sumofproducts : {
  val red [n] : [n]u8 -> f64
  val split_consistent [n] : [n]u8 -> bool
  val association_consistent [n] : [n]u8 -> bool
  val nested_failure_left : bool -> f64
  val nested_failure_right : bool -> f64
  val red2 [n] : [n]u8 -> f64
  val split2_consistent [n] : [n]u8 -> bool
  val association2_consistent [n] : [n]u8 -> bool
  val red3 [n] : [n]u8 -> f64
  val split3_consistent [n] : [n]u8 -> bool
} = {
  open monoidal

  module groups = chunk (sum f64) (optone f64) { def del_ign (c:u8) = c == '+' }
  module items = chunk (mul f64) groups { def del_ign (c:u8) = c == '*' }
  module Expr = chunk (float f64) items { def del_ign (_:u8) = false }

  module Outer0 = chunk (nestable (float f64)) items { def del_ign (_:u8) = false }
  module Outer = with_gen Outer0 {
    type i = nest Expr.i Expr.o
    def gen (x:i) : Outer0.i =
      match x
      case #Raw (#E c) -> #E (#Raw c)
      case #Raw (#Del c) -> #Del c
      case #Nested x -> #E (#Nested x)
  }

  module P = parens Expr Outer {
    def left (c:u8) = c == '('
    def right (c:u8) = c == ')'
  }
  module T = with_gen P {
    type i = u8
    def gen (c:i) : P.i =
      if c == '(' || c == ')' then #Del c
      else if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E (#E c)
      else #E (#Del c)
  }

  module R0 = Parens.Zero { type t = Outer.t }
  module R1 = Parens.Succ R0
  module R2 = Parens.Succ R1
  module R3 = Parens.Succ R2
  module P2 = Parens.Make
    { type raw = Expr.i type value = f64 } Outer R2 {
    def left (c:u8) = c == '('
    def right (c:u8) = c == ')'
  }
  module T2 = with_gen P2 {
    type i = u8
    def gen (c:i) : P2.i =
      if c == '(' || c == ')' then #Del c
      else if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E (#E c)
      else #E (#Del c)
  }

  module P3 = Parens.Make
    { type raw = Expr.i type value = f64 } Outer R3 {
    def left (c:u8) = c == '('
    def right (c:u8) = c == ')'
  }
  module T3 = with_gen P3 {
    type i = u8
    def gen (c:i) : P3.i =
      if c == '(' || c == ')' then #Del c
      else if ('0' <= c && c <= '9') || c == '.' || c == '-' then #E (#E c)
      else #E (#Del c)
  }

  def red [n] (xs:[n]u8) : f64 =
    reduce T.op T.ne (map T.gen xs) |> T.obs

  -- Check every possible two-way partition.  Each side is reduced
  -- independently before their summaries are combined, so split points on
  -- either side of a parenthesis exercise the boundary states in `parens`.
  def split_consistent [n] (xs:[n]u8) : bool =
    let expected = red xs
    let parts = map T.gen xs
    let agrees (i:i64) =
      let l = reduce T.op T.ne parts[:i]
      let r = reduce T.op T.ne parts[i:]
      in T.obs (T.op l r) == expected
    in reduce (&&) true (map agrees (iota (n+1)))

  def association_consistent [n] (xs:[n]u8) : bool =
    let parts = map T.gen xs
    let agrees_i (i:i64) =
      let agrees_j (j:i64) =
        let a = reduce T.op T.ne parts[:i]
        let b = reduce T.op T.ne parts[i:j]
        let c = reduce T.op T.ne parts[j:]
        in T.obs (T.op (T.op a b) c) == T.obs (T.op a (T.op b c))
      in reduce (&&) true (map agrees_j (map (\j -> i+j) (iota (n-i+1))))
    in reduce (&&) true (map agrees_i (iota (n+1)))

  -- The old four-form implementation forgot the depth excursion in the
  -- right-associated case `(` op (`(` op `)`).  Both associations now
  -- produce the same canonical invalid summary.
  def nested_failure_left (_:bool) : f64 =
    let l = T.gen '('
    let r = T.gen ')'
    in T.obs (T.op (T.op l l) r)

  def nested_failure_right (_:bool) : f64 =
    let l = T.gen '('
    let r = T.gen ')'
    in T.obs (T.op l (T.op l r))

  def red2 [n] (xs:[n]u8) : f64 =
    reduce T2.op T2.ne (map T2.gen xs) |> T2.obs

  def split2_consistent [n] (xs:[n]u8) : bool =
    let expected = red2 xs
    let parts = map T2.gen xs
    let agrees (i:i64) =
      let l = reduce T2.op T2.ne parts[:i]
      let r = reduce T2.op T2.ne parts[i:]
      in T2.obs (T2.op l r) == expected
    in reduce (&&) true (map agrees (iota (n+1)))

  def association2_consistent [n] (xs:[n]u8) : bool =
    let parts = map T2.gen xs
    let agrees_i (i:i64) =
      let agrees_j (j:i64) =
        let a = reduce T2.op T2.ne parts[:i]
        let b = reduce T2.op T2.ne parts[i:j]
        let c = reduce T2.op T2.ne parts[j:]
        let l = T2.obs (T2.op (T2.op a b) c)
        let r = T2.obs (T2.op a (T2.op b c))
        in l == r
      in reduce (&&) true (map agrees_j (map (\j -> i+j) (iota (n-i+1))))
    in reduce (&&) true (map agrees_i (iota (n+1)))

  def red3 [n] (xs:[n]u8) : f64 =
    reduce T3.op T3.ne (map T3.gen xs) |> T3.obs

  def split3_consistent [n] (xs:[n]u8) : bool =
    let expected = red3 xs
    let parts = map T3.gen xs
    let agrees (i:i64) =
      let l = reduce T3.op T3.ne parts[:i]
      let r = reduce T3.op T3.ne parts[i:]
      in T3.obs (T3.op l r) == expected
    in reduce (&&) true (map agrees (iota (n+1)))
}

entry test_parenthesised_sumofproducts [n] (xs:[n]u8) : f64 =
  parenthesised_sumofproducts.red xs

entry test_parenthesised_sumofproducts_splits [n] (xs:[n]u8) : bool =
  parenthesised_sumofproducts.split_consistent xs

entry test_parenthesised_sumofproducts_association [n] (xs:[n]u8) : bool =
  parenthesised_sumofproducts.association_consistent xs

entry test_parenthesised_nested_failure_left (trigger:bool) : f64 =
  parenthesised_sumofproducts.nested_failure_left trigger

entry test_parenthesised_nested_failure_right (trigger:bool) : f64 =
  parenthesised_sumofproducts.nested_failure_right trigger

entry test_parenthesised_sumofproducts2 [n] (xs:[n]u8) : f64 =
  parenthesised_sumofproducts.red2 xs

entry test_parenthesised_sumofproducts2_splits [n] (xs:[n]u8) : bool =
  parenthesised_sumofproducts.split2_consistent xs

entry test_parenthesised_sumofproducts2_association [n] (xs:[n]u8) : bool =
  parenthesised_sumofproducts.association2_consistent xs

entry test_parenthesised_sumofproducts3 [n] (xs:[n]u8) : f64 =
  parenthesised_sumofproducts.red3 xs

entry test_parenthesised_sumofproducts3_splits [n] (xs:[n]u8) : bool =
  parenthesised_sumofproducts.split3_consistent xs

-- Tests of parenthesised_sumofproducts
-- ==
-- entry: test_parenthesised_sumofproducts
-- input { "34" }
-- output { 34f64 }
-- input { "(34)" }
-- output { 34f64 }
-- input { "(2+3)*4" }
-- output { 20f64 }
-- input { "2*(3+4)" }
-- output { 14f64 }
-- input { "2*(3+4)+5" }
-- output { 19f64 }
-- input { "(2+3)*(4+5)" }
-- output { 45f64 }
-- input { "(2*3)+(4*5)" }
-- output { 26f64 }
-- input { "1+(2*3)+4" }
-- output { 11f64 }
-- input { "1+2*(3+4)*5+6" }
-- output { 77f64 }
-- input { "(-2+3.5)*4" }
-- output { 6f64 }
-- input { "2+3*(4+5)+6*(7+8)+9" }
-- output { 128f64 }
-- input { "12*(34+56)+78" }
-- output { 1158f64 }
-- input { "(12+34)*(56+78)" }
-- output { 6164f64 }
-- input { "(12*34)+(56*78)" }
-- output { 4776f64 }
-- input { "100+25*(30+4)*2+7" }
-- output { 1807f64 }
-- input { "12.5*(30+2)+100" }
-- output { 500f64 }

-- Test every possible boundary between independently reduced substrings.
-- entry: test_parenthesised_sumofproducts_splits
-- input { "34" }
-- output { true }
-- input { "(34)" }
-- output { true }
-- input { "2*(3+4)+5" }
-- output { true }
-- input { "(2+3)*(4+5)" }
-- output { true }
-- input { "(2*3)+(4*5)" }
-- output { true }
-- input { "1+2*(3+4)*5+6" }
-- output { true }
-- input { "2+3*(4+5)+6*(7+8)+9" }
-- output { true }
-- input { "12*(34+56)+78" }
-- output { true }
-- input { "(12+34)*(56+78)" }
-- output { true }
-- input { "100+25*(30+4)*2+7" }
-- output { true }

-- Exercise both associations at every three-way split.  The final example
-- includes adjacent `B`-form fragments for suitable split points.
-- entry: test_parenthesised_sumofproducts_association
-- input { "2*(3+4)+5" }
-- output { true }
-- input { "(1)+(2)+(3)" }
-- output { true }
-- input { "12*(34+56)+78" }
-- output { true }

-- Both associations of the former counterexample must now reject.
-- entry: test_parenthesised_nested_failure_left
-- input { true }
-- error:

-- entry: test_parenthesised_nested_failure_right
-- input { true }
-- error:

-- Tests of two parenthesis levels.
-- entry: test_parenthesised_sumofproducts2
-- input { "34" }
-- output { 34f64 }
-- input { "2*(3+4)" }
-- output { 14f64 }
-- input { "2*(3+(4*5))" }
-- output { 46f64 }
-- input { "((2+3)*4)" }
-- output { 20f64 }
-- input { "(2+(3*4))*(5+(6*7))" }
-- output { 658f64 }
-- input { "12*(34+56*(2+3))+78" }
-- output { 3846f64 }
-- The following expression reaches depth three and must be rejected at
-- depth two.
-- input { "12*(34+(56*(2+3)))+78" }
-- error:

-- Check all two-way reduction splits, including splits between adjacent
-- opening and closing parentheses.
-- entry: test_parenthesised_sumofproducts2_splits
-- input { "2*(3+(4*5))" }
-- output { true }
-- input { "((2+3)*4)" }
-- output { true }
-- input { "(2+(3*4))*(5+(6*7))" }
-- output { true }
-- input { "12*(34+56*(2+3))+78" }
-- output { true }

-- Instantiate the general combinator at depth three.
-- entry: test_parenthesised_sumofproducts3
-- input { "(((2+3)*4)+5)" }
-- output { 25f64 }
-- input { "2*(3+(4*(5+6)))" }
-- output { 94f64 }
-- input { "12*(34+(56*(2+3*4)))+78" }
-- output { 9894f64 }
-- input { "12*(34+(56*(2+3)))+78" }
-- output { 3846f64 }

-- entry: test_parenthesised_sumofproducts3_splits
-- input { "(((2+3)*4)+5)" }
-- output { true }
-- input { "2*(3+(4*(5+6)))" }
-- output { true }
-- input { "12*(34+(56*(2+3*4)))+78" }
-- output { true }
-- input { "12*(34+(56*(2+3)))+78" }
-- output { true }

-- Exercise both associations of every three-way split.
-- entry: test_parenthesised_sumofproducts2_association
-- input { "2*(3+(4*5))" }
-- output { true }
-- input { "((2+3)*4)" }
-- output { true }
-- input { "(2+(3*4))*(5+(6*7))" }
-- output { true }
