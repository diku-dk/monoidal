-- | Library of composable monoids. The library allows for processing
-- formatted byte sequences using a single monoidal operation. Examples include
-- finding the maximum average of grouped floats. The library is heavily
-- inspired by Oleg Kiselyov's paper
-- [More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
-- and the associated OCaml code.

-- | The option type
type opt 'a = #some a | #none

-- | Type representing a delimiter or an element value
type del 'a = #E a | #Del u8.t

-- | An ordinary input value or the result of evaluating a nested monoid.
type nest 'a 'b = #Raw a | #Nested b

-- | Module type representing a composable monoid. A composable monoid is
-- equipped with an "injection operation" `gen` for injecting a value into the
-- monoid type and a "projection operation" `obs` for observing a value in the
-- monoid type.
module type monoid = {
  type t
  val ne : t
  val op : t -> t -> t
  type i
  val gen : i -> t
  type o
  val obs : t -> o
}

local
-- | Internal interface for selecting how a parser reports failure.
module type failure = {
  type result 'a
  val ok 'a : a -> result a
  val fail 'a : bool -> a -> result a
  val bind 'a 'b : result a -> (a -> result b) -> result b
  val bind2 'a 'b 'c : (a -> b -> result c) -> result a -> result b -> result c
}

-- | Module type representing module combinators for composing monoids.
module type monoidal = {

  -- | Monoid for constructing natural numbers. Initial zeros are allowed.
  module nat   : (Y:numeric) -> monoid with i = u8 with o = Y.t

  -- | Monoid for constructing floating point values. Initial zeros and trailing
  -- zeros are allowed. The format of floats is flexible. For instance, the
  -- character sequence '-.' is considered a valid float (0.0).
  module float : (Y:numeric) -> monoid with i = u8 with o = Y.t

  -- | Total variant of `float`.  Malformed or incomplete floating-point
  -- values are observed as `#none`.
  module float_try : (Y:numeric) -> monoid with i = u8 with o = opt Y.t

  -- | Chunking combinator for creating nested monoids. When `X = chunk M1 M2
  -- D`, `M2` will be treated as an "inner monoid", which consumes elements when
  -- they become available from the "outer monoid" `M1`. The `D.del_ign`
  -- operation specifies a deliminator for the resulting monoid.
  module chunk : (M1:monoid) -> (M2:monoid with i = del M1.o) -> { val del_ign : u8 -> bool }
		 -> monoid with i = del M1.i with o = M2.o

  -- | The summation monoid.
  module sum   : (Y:numeric) -> monoid with i = Y.t with o = Y.t

  -- | The multiplication monoid.
  module mul   : (Y:numeric) -> monoid with i = Y.t with o = Y.t

  -- | The maximum monoid.
  module max   : (Y:numeric) -> monoid with i = Y.t with o = Y.t

  -- | The minimum monoid.
  module min   : (Y:numeric) -> monoid with i = Y.t with o = Y.t

  -- | The boolean monoid all
  module all   : monoid with i = bool with o = bool

  -- | The boolean monoid exists
  module exists : monoid with i = bool with o = bool

  -- | Combinator for parallel composition.
  module prod  : (M1:monoid) -> (M2:monoid) -> monoid with i = (M1.i,M2.i) with o = (M1.o,M2.o)

  -- | Try two total monoids on the same input in parallel.  Observation
  -- prefers the result from `M1` when both succeed, and otherwise returns
  -- the successful result from `M2` (or `#none` when both fail).
  module or : (X:{type t}) -> (M1:monoid with o = opt X.t)
              -> (M2:monoid with i = M1.i with o = opt X.t)
              -> monoid with t = (M1.t,M2.t)
                        with i = M1.i with o = opt X.t

  -- | Combinator for extending monoid injection.
  module with_gen : (M: monoid) -> (X:{ type i val gen : i -> M.i }) -> monoid with o = M.o with i = X.i

  -- | Combinator for extending monoid projection.
  module with_obs : (M: monoid) -> (X:{ type o val obs : M.o -> o }) -> monoid with i = M.i with o = X.o

  -- | Filtering
  module filter : (M: monoid) -> { val pred : M.o -> bool } -> monoid with i = M.i with o = M.o

  -- | Duplication monoid.
  module dup  : (X:{type i}) -> (M:monoid with i = (X.i,X.i)) -> monoid with i = X.i with o = M.o

  -- | Counting monoid.
  module count : (X:{type i}) -> monoid with i = X.i with o = i64

  -- | Option monoid.
  module opt : (M:monoid) -> monoid with i = opt M.i with o = opt M.o

  -- | Monoid failing on empty data.
  module one : (X:{type t}) -> monoid with i = X.t with o = X.t

  -- | Monoid failing on empty data and on delimiters.
  module optone : (X:{type t}) -> monoid with i = del X.t with o = X.t

  -- | Extend a monoid so an already-observed value can be injected as a
  -- single input value.
  module nestable : (M:monoid) -> monoid with i = nest M.i M.o with o = M.o

  -- | Nest `M1` inside `M2` between one level of parentheses.  `M2` receives
  -- ordinary inputs as `#Raw` and each completed parenthesised value as
  -- `#Nested`.  Nested parentheses are not supported.
  module parens : (M1:monoid) -> (M2:monoid with i = nest M1.i M1.o)
                  -> { val left : u8 -> bool val right : u8 -> bool }
                  -> monoid with i = del M1.i with o = M2.o

  -- | Nest a monoid under at most `N.n` levels of parentheses, where `N.n`
  -- must be non-negative.  The same monoid is used at every level: raw values
  -- are injected with `#Raw`, while the value of a completed parenthesised
  -- region is injected with `#Nested`.
  module parens_n : (_N:{val n : i64}) -> (X:{type raw type value})
                    -> (_M:monoid with i = nest X.raw X.value with o = X.value)
                    -> { val left : u8 -> bool val right : u8 -> bool }
                    -> monoid with i = del X.raw with o = X.value

}

module monoidal = {

  def ERR_op_F_and_P_do_not_reduce = false
  def ERR_op_P_and_PF_do_not_reduce = false
  def ERR_op_F_and_F_do_not_reduce = false
  def ERR_op_PIFM_and_M_do_not_reduce = false
  def ERR_obs_expecting_I_or_F_got_NE = false
  def ERR_obs_expecting_I_or_F_got_P = false
  def ERR_obs_expecting_I_or_F_got_M = false
  def ERR_gen_expecting_E = false
  def ERR_obs_expecting_some = false
  def ERR_nestable_values_do_not_combine = false
  def ERR_nested_parentheses = false
  def ERR_unbalanced_parentheses = false

  module mk_simple_num (X:numeric) (Y: { val op : X.t -> X.t -> X.t val ne : X.t })
	 : monoid with i = X.t with o = X.t = {
    type t = X.t
    def op = Y.op
    def ne = Y.ne
    type i = t
    def gen x : t = x
    type o = t
    def obs x : o = x
  }

  module sum (X:numeric) = mk_simple_num X { def ne = X.i8 0 def op = (X.+) }
  module mul (X:numeric) = mk_simple_num X { def ne = X.i8 1 def op = (X.*) }
  module max (X:numeric) = mk_simple_num X { def ne = X.lowest def op = (X.max) }
  module min (X:numeric) = mk_simple_num X { def ne = X.highest def op = (X.min) }

  module mk_simple_bool (Y: { val op : bool -> bool -> bool val ne : bool })
	 : monoid with i = bool with o = bool = {
    type t = bool
    def op = Y.op
    def ne = Y.ne
    type i = t
    def gen x : t = x
    type o = t
    def obs x : o = x
  }

  module all = mk_simple_bool { def op a b = a && b def ne = true }
  module exists = mk_simple_bool { def op a b = a || b def ne = false }

  module count (X : { type i }) : monoid with i = X.i with o = i64 = {
    type t = i64
    def ne : t = 0
    def op = (i64.+)
    type i = X.i
    def gen (_ : i) : t = 1
    type o = t
    def obs (x:t) = x
  }

  module one (X: { type t }) : monoid with i = X.t with o = X.t = {
    type t = opt X.t
    type i = X.t
    def ne : t = #none
    def op (x:t) (y:t) : t =
      match x
      case #some _ -> x
      case _ -> y
    def gen x : t = #some x
    type o = X.t
    def obs (x:t) : o =
      match x
      case #some x -> x
      case #none -> assert ERR_obs_expecting_some (([])[0])
  }

  module opt (M:monoid) : monoid with i = opt M.i with o = opt M.o = {
    type t = opt M.t
    def ne : t = #none
    def op (x:t) (y:t) : t =
      match x
      case #some _ -> x
      case _ -> y
    type i = opt M.i
    def gen (x:i) : t =
      match x case #none -> #none case #some x -> #some (M.gen x)
    type o = opt M.o
    def obs (x:t) : o =
      match x case #none -> #none case #some x -> #some (M.obs x)
  }

  module prod (M1:monoid) (M2:monoid) : monoid with i = (M1.i,M2.i) with o = (M1.o,M2.o) = {
    type t = (M1.t,M2.t)
    def ne : t = (M1.ne,M2.ne)
    def op ((x1,y1):t) ((x2,y2):t) : t = (M1.op x1 x2, M2.op y1 y2)
    type i = (M1.i,M2.i)
    def gen ((x,y):i) : t = (M1.gen x, M2.gen y)
    type o = (M1.o,M2.o)
    def obs ((x,y):t) = (M1.obs x, M2.obs y)
  }

  module or (X:{type t})
            (M1:monoid with o = opt X.t)
            (M2:monoid with i = M1.i with o = opt X.t)
      : monoid with t = (M1.t,M2.t)
                 with i = M1.i with o = opt X.t = {
    type t = (M1.t,M2.t)
    def ne : t = (M1.ne,M2.ne)
    def op ((x1,y1):t) ((x2,y2):t) : t =
      (M1.op x1 x2, M2.op y1 y2)
    type i = M1.i
    def gen (x:i) : t = (M1.gen x, M2.gen x)
    type o = opt X.t
    def obs ((x,y):t) : o =
      match M1.obs x
      case #some v -> #some v
      case #none -> M2.obs y
  }

  module with_gen (M:monoid) (X:{ type i val gen : i -> M.i }) : monoid with o = M.o with i = X.i = {
    open M
    type i = X.i
    def gen (i:i) : t = gen(X.gen i)
  }

  module with_obs (M:monoid) (X:{ type o val obs : M.o -> o }) : monoid with i = M.i with o = X.o = {
    open M
    type o = X.o
    def obs (x:t) : o = X.obs(obs x)
  }

  module optone (X: { type t }) : monoid with i = del X.t with o = X.t =
    with_gen (one X) {
      type i = del X.t
      def ERR_gen_expecting_E = false
      def gen (i:del X.t) : X.t =
	match i case #E x -> x
		case #Del _ -> assert ERR_gen_expecting_E (([])[0])
    }

  module nestable (M:monoid) : monoid with i = nest M.i M.o with o = M.o = {
    type t = #NE | #M M.t | #V M.o
    def ne : t = #NE
    def op (x:t) (y:t) : t =
      match (x,y)
      case (#NE, _) -> y
      case (_, #NE) -> x
      case (#M x, #M y) -> #M (M.op x y)
      case _ -> assert ERR_nestable_values_do_not_combine (#NE)
    type i = nest M.i M.o
    def gen (x:i) : t =
      match x
      case #Raw x -> #M (M.gen x)
      case #Nested x -> #V x
    type o = M.o
    def obs (x:t) : o =
      match x
      case #NE -> M.obs M.ne
      case #M x -> M.obs x
      case #V x -> x
  }

  module filter (M:monoid) (X:{ val pred : M.o -> bool }) : monoid with i = M.i with o = M.o =
    with_obs M { type o = M.o
                 def obs (x:M.o) : o =
                   if X.pred x then x
		   else M.obs M.ne
               }

  module dup (X:{ type i }) (M:monoid with i = (X.i,X.i)) : monoid with i = X.i with o = M.o =
    with_gen M { type i = X.i def gen (i:i) = (i,i) }

  module nat (Y:numeric) : monoid with i = u8 with o = Y.t = {
    type t = (Y.t,Y.t)
    def ne : t = (Y.i8 0, Y.i8 1)
    def op (x,b1) (y,b2) = Y.((x * b2 + y, b1 * b2))
    type i = u8
    def gen (x:i) : t = Y.((u8 x - u8 '0', i8 10))
    type o = Y.t
    def obs (x:t) : o = x.0
  }

  module assert_failure = {
    type result 'a = a
    def ok 'a (x:a) : result a = x
    def fail 'a (_:bool) (x:a) : result a = assert false x
    def bind 'a 'b (x:result a) (f:a -> result b) : result b = f x
    def bind2 'a 'b 'c (f:a -> b -> result c) (x:result a) (y:result b) : result c = f x y
  }

  module option_failure = {
    type result 'a = opt a
    def ok 'a (x:a) : result a = #some x
    def fail 'a (_:bool) (_:a) : result a = #none
    def bind 'a 'b (x:result a) (f:a -> result b) : result b =
      match x case #some x -> f x case #none -> #none
    def bind2 'a 'b 'c (f:a -> b -> result c) (x:result a) (y:result b) : result c =
      match (x,y)
      case (#some x, #some y) -> f x y
      case _ -> #none
  }

  module float0 (Y:numeric) (Fail:failure)
      : monoid with i = u8 with o = Fail.result Y.t = {
    type raw_t = #I (bool,Y.t,Y.t)
	   | #F (bool,Y.t,Y.t,Y.t)
	   | #P               -- period
	   | #M               -- minus
	   | #NE              -- neutral element
    type t = Fail.result raw_t
    type o = Fail.result Y.t
    type i = u8.t
    def ne : t = Fail.ok #NE
    def raw_op (a:raw_t) (b:raw_t) : Fail.result raw_t =
      match (a,b)
      case (#NE, _) -> Fail.ok b
      case (_, #NE) -> Fail.ok a
      case (#I(s1,x,b1), #I(s2,y,b2)) ->
	if !s2 then Fail.ok (#I(Y.((s1, x * b2 + y, b1 * b2))))
	else Fail.fail false #NE
      case (#I(s1,x,b1), #F(s2,y,b2,f2)) ->
	if !s2 then Fail.ok (#F(Y.((s1, x * b2 + y, b1 * b2, f2))))
	else Fail.fail false #NE
      case (#F(s1,x,b1,f1), #I(s2,y,b2)) ->
	if !s2 then Fail.ok (#F(Y.((s1, x + y * f1, b1, f1 / b2))))
	else Fail.fail false #NE
      case (#I(s,x,b), #P) -> Fail.ok (#F(Y.((s, x, b, u8 1 / u8 10))))
      case (#P, #I(s,x,b)) ->
	if !s then Fail.ok (#F(Y.((false, x / b, u8 1, u8 1 / b))))
	else Fail.fail false #NE
      case (#M, #I(s,x,b)) ->
	if !s then Fail.ok (#I(true,x,b)) else Fail.fail false #NE
      case (#M, #F(s,x,b,f)) ->
	if !s then Fail.ok (#F(true,x,b,f)) else Fail.fail false #NE
      case (#M, #P) -> Fail.ok (#F(Y.((true, u8 0, u8 1, u8 1 / u8 10))))
      case (#F _, #P) -> Fail.fail ERR_op_F_and_P_do_not_reduce #NE
      case (#P, #F _) -> Fail.fail ERR_op_P_and_PF_do_not_reduce #NE
      case (#P, #P) -> Fail.fail ERR_op_P_and_PF_do_not_reduce #NE
      case (#F _, #F _) -> Fail.fail ERR_op_F_and_F_do_not_reduce #NE
      case (#P, #M) -> Fail.fail ERR_op_PIFM_and_M_do_not_reduce #NE
      case (#I _, #M) -> Fail.fail ERR_op_PIFM_and_M_do_not_reduce #NE
      case (#F _, #M) -> Fail.fail ERR_op_PIFM_and_M_do_not_reduce #NE
      case (#M, #M) -> Fail.fail ERR_op_PIFM_and_M_do_not_reduce #NE
    def op (a:t) (b:t) : t = Fail.bind2 raw_op a b
    def raw_obs (x:raw_t) : o =
      match x
      case #I(s,x,_) -> Fail.ok (if s then Y.neg x else x)
      case #F(s,x,_,_) -> Fail.ok (if s then Y.neg x else x)
      case #NE -> Fail.fail ERR_obs_expecting_I_or_F_got_NE (Y.i8 0)
      case #P -> Fail.fail ERR_obs_expecting_I_or_F_got_P (Y.i8 0)
      case #M -> Fail.fail ERR_obs_expecting_I_or_F_got_M (Y.i8 0)
    def obs (x:t) : o = Fail.bind x raw_obs
    def gen (x:i) : t =
      if x == '.' then Fail.ok #P
      else if x == '-' then Fail.ok #M
      else if '0' <= x && x <= '9' then
	Fail.ok (#I(Y.((false, u8 x - u8 '0', u8 10))))
      else Fail.fail false #NE
  }

  module float (Y:numeric) : monoid with i = u8 with o = Y.t =
    float0 Y assert_failure

  module float_try (Y:numeric) : monoid with i = u8 with o = opt Y.t =
    float0 Y option_failure

  module chunk (M1: monoid)
	       (M2: monoid with i = del M1.o)
	       (X: { val del_ign : u8 -> bool })
	 : monoid with i = del M1.i with o = M2.o = {
    type t = #A M1.t | #C (M1.t, M2.t, M1.t) -- chunk
    def ne : t = #A M1.ne
    def m1_to_m2 (x:M1.t) : M2.t = M2.gen (#E(M1.obs x))
    def op (x:t) (y:t) : t =
      match (x,y)
      case (#A lx, #A ly) -> #A(M1.op lx ly)
      case (#A lx, #C (l,c,r)) -> #C(M1.op lx l,c,r)
      case (#C (lx,cx,rx), #A ly) -> #C(lx,cx,M1.op rx ly)
      case (#C (lx,cx,rx), #C (ly,cy,ry)) ->
	#C(lx, M2.op cx (M2.op (m1_to_m2(M1.op rx ly)) cy), ry)
    type i = del M1.i
    def gen (i:i) : t =
      match i
      case #E x -> #A (M1.gen x)
      case #Del c ->
	if X.del_ign c then #A M1.ne
	else #C (M1.ne, M2.gen (#Del c), M1.ne)
    type o = M2.o
    def obs (x:t) : o =
      match x
      case #A x -> m1_to_m2 x |> M2.obs
      case #C (l,c,r) -> M2.((op (m1_to_m2 l) (op c (m1_to_m2 r))) |> obs)
  }

  module parens (M1:monoid)
                (M2:monoid with i = nest M1.i M1.o)
                (X:{ val left : u8 -> bool val right : u8 -> bool })
      : monoid with i = del M1.i with o = M2.o = {
    -- `A` contains no parenthesis boundary and keeps both possible
    -- interpretations: inside M1 and outside M2.  The other constructors
    -- describe an unmatched left boundary, right boundary, or both.
    type t = #A (M1.t, M2.t)
           | #L (M2.t, M1.t)
           | #R (M1.t, M2.t)
           | #B (M1.t, M2.t, M1.t)
    def ne : t = #A (M1.ne, M2.ne)
    def close (x:M1.t) : M2.t = M2.gen (#Nested (M1.obs x))
    def op (x:t) (y:t) : t =
      match (x,y)
      case (#A (xi,xo), #A (yi,yo)) ->
        #A (M1.op xi yi, M2.op xo yo)
      case (#A (_,xo), #L (yo,yi)) -> #L (M2.op xo yo, yi)
      case (#L (xo,xi), #A (yi,_)) -> #L (xo, M1.op xi yi)
      case (#A (xi,_), #R (yi,yo)) -> #R (M1.op xi yi, yo)
      case (#R (xi,xo), #A (_,yo)) -> #R (xi, M2.op xo yo)
      case (#A (xi,_), #B (yl,yo,yr)) -> #B (M1.op xi yl, yo, yr)
      case (#B (xl,xo,xr), #A (yi,_)) -> #B (xl, xo, M1.op xr yi)
      case (#L (xo,xi), #R (yi,yo)) ->
        #A (M1.ne, M2.op xo (M2.op (close (M1.op xi yi)) yo))
      case (#R (xi,xo), #L (yo,yi)) -> #B (xi, M2.op xo yo, yi)
      case (#L (xo,xi), #B (yi,yo,yr)) ->
        #L (M2.op xo (M2.op (close (M1.op xi yi)) yo), yr)
      case (#B (xl,xo,xr), #R (yi,yo)) ->
        #R (xl, M2.op xo (M2.op (close (M1.op xr yi)) yo))
      case _ -> assert ERR_nested_parentheses ne
    type i = del M1.i
    def gen (x:i) : t =
      match x
      case #E x -> #A (M1.gen x, M2.gen (#Raw x))
      case #Del c ->
        if X.left c then #L (M2.ne, M1.ne)
        else if X.right c then #R (M1.ne, M2.ne)
        else #A (M1.ne, M2.ne)
    type o = M2.o
    def obs (x:t) : o =
      match x
      case #A (_,x) -> M2.obs x
      case _ -> assert ERR_unbalanced_parentheses (M2.obs M2.ne)
  }

  module parens_n
      (N:{val n : i64})
      (X:{type raw type value})
      (M:monoid with i = nest X.raw X.value with o = X.value)
      (D:{ val left : u8 -> bool val right : u8 -> bool })
      : monoid with i = del X.raw with o = X.value = {
    -- Every segment is normalised to
    --
    --   r0 ) r1 ... ) rc ( r... ( r(c+o)
    --
    -- A depth bound of n requires 2*n+1 region slots: a viable segment can
    -- contain n unmatched closing parentheses followed by n unmatched
    -- opening parentheses.  `lo`, `hi`, and `net` describe the relative
    -- parenthesis depth of the original segment.
    type regions = [2*N.n+1]M.t
    type t = { valid: bool,
               lo: i64, hi: i64, net: i64,
               closes: i64, opens: i64,
               regions: regions }

    def empty_regions () : regions = replicate (2*N.n+1) M.ne

    def region (rs:regions) (i:i64) : M.t = rs[i]

    def put_region (rs:regions) (i:i64) (x:M.t) : regions =
      map2 (\j y -> if j == i then x else y) (iota (2*N.n+1)) rs

    def base (x:M.t) : t =
      { valid = true, lo = 0, hi = 0, net = 0,
        closes = 0, opens = 0,
        regions = put_region (empty_regions ()) 0 x }

    def invalid () : t =
      { valid = false, lo = 0, hi = 0, net = 0,
        closes = 0, opens = 0, regions = empty_regions () }
    def ne : t = base M.ne

    def append_region (s:t) (x:M.t) : t =
      let i = s.closes + s.opens
      let old = region s.regions i
      in { valid = s.valid, lo = s.lo, hi = s.hi, net = s.net,
           closes = s.closes, opens = s.opens,
           regions = put_region s.regions i (M.op old x) }

    def append_open (s:t) : t =
      let i = s.closes + s.opens + 1
      in { valid = s.valid, lo = s.lo, hi = s.hi, net = s.net,
           closes = s.closes, opens = s.opens + 1,
           regions = put_region s.regions i M.ne }

    def append_close (s:t) : t =
      if s.opens > 0 then
        let i = s.closes + s.opens
        let inner = region s.regions i
        let outer = region s.regions (i-1)
        let nested = M.gen (#Nested (M.obs inner))
        let rs = put_region s.regions (i-1) (M.op outer nested)
        in { valid = s.valid, lo = s.lo, hi = s.hi, net = s.net,
             closes = s.closes, opens = s.opens - 1, regions = rs }
      else
        let i = s.closes + 1
        in { valid = s.valid, lo = s.lo, hi = s.hi, net = s.net,
             closes = s.closes + 1, opens = s.opens,
             regions = put_region s.regions i M.ne }

    def op (a:t) (b:t) : t =
      let lo = i64.min a.lo (a.net + b.lo)
      let hi = i64.max a.hi (a.net + b.hi)
      let net = a.net + b.net
      in if !a.valid || !b.valid || hi-lo > N.n then invalid ()
         else
           let s0 = append_region a (region b.regions 0)
           let s1 = loop s = s0 for j < b.closes do
                      append_region (append_close s)
                                    (region b.regions (j+1))
           let s2 = loop s = s1 for j < b.opens do
                      append_region (append_open s)
                                    (region b.regions (b.closes+j+1))
           in { valid = s2.valid, lo = lo, hi = hi, net = net,
                closes = s2.closes, opens = s2.opens,
                regions = s2.regions }

    type i = del X.raw
    def gen (x:i) : t =
      match x
      case #E x -> base (M.gen (#Raw x))
      case #Del c ->
        if D.left c then
          if N.n == 0 then invalid ()
          else append_open (base M.ne)
               |> (\s -> { valid = s.valid, lo = 0, hi = 1, net = 1,
                            closes = s.closes, opens = s.opens,
                            regions = s.regions })
        else if D.right c then
          if N.n == 0 then invalid ()
          else append_close (base M.ne)
               |> (\s -> { valid = s.valid, lo = -1, hi = 0, net = -1,
                            closes = s.closes, opens = s.opens,
                            regions = s.regions })
        else base M.ne

    type o = X.value
    def obs (s:t) : o =
      if s.valid && s.lo >= 0 && s.hi <= N.n && s.net == 0 &&
         s.closes == 0 && s.opens == 0
      then M.obs (region s.regions 0)
      else assert ERR_unbalanced_parentheses (M.obs M.ne)
  }

}
