import "monoidal"

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
-- script input { $loadbytes "ex.txt" }
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
-- script input { $loadbytes "ex.txt" }
-- output { 908.71f64 }

entry bench_max_avgs [n] (xs: [n]u8) : f64 =
  max_avgs.red xs

-- Bench of max_avgs
-- ==
-- entry: bench_max_avgs
-- script notest input { $loadbytes "ex.txt" }
-- output { 908.71f64 }
-- script notest input { $loadbytes "../../../../util/ex50.txt" }
-- output { 866.25 }
-- script notest input { $loadbytes "../../../../util/ex100.txt" }
-- output { 989.5714285714286 }
-- script notest input { $loadbytes "../../../../util/ex200.txt" }
-- output { 1028.0 }
-- script notest input { $loadbytes "../../../../util/ex400.txt" }
-- output { 1225.25 }
-- script notest input { $loadbytes "../../../../util/ex800.txt" }
-- output { 1056.142857142857 }
-- script notest input { $loadbytes "../../../../util/ex1600.txt" }
-- output { 1092.5714285714287 }
-- script notest input { $loadbytes "../../../../util/ex3200.txt" }
-- output { 1100.75 }
-- script notest input { $loadbytes "../../../../util/ex6400.txt" }
-- output { 1070.4285714285713 }
-- script notest input { $loadbytes "../../../../util/ex12800.txt" }
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
