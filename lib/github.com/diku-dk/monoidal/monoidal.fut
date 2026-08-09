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
-- | Module type representing module combinators for composing monoids.
module type monoidal = {

  -- | Monoid for constructing natural numbers. Initial zeros are allowed.
  module nat   : (Y:numeric) -> monoid with i = u8 with o = Y.t

  -- | Monoid for constructing floating point values. Initial zeros and trailing
  -- zeros are allowed. The format of floats is flexible. For instance, the
  -- character sequence '-.' is considered a valid float (0.0).
  module float : (Y:numeric) -> monoid with i = u8 with o = Y.t

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

  module with_gen (M:monoid) (X:{ type i val gen : i -> M.i }) : monoid with o = M.o with i = X.i = {
    open M
    type i = X.i
    def gen (i:i) : t = M.gen(X.gen i)
  }

  module with_obs (M:monoid) (X:{ type o val obs : M.o -> o }) : monoid with i = M.i with o = X.o = {
    open M
    type o = X.o
    def obs (x:t) : o = X.obs(M.obs x)
  }

  module optone (X: { type t }) : monoid with i = del X.t with o = X.t =
    with_gen (one X) {
      type i = del X.t
      def ERR_gen_expecting_E = false
      def gen (i:del X.t) : X.t =
	match i case #E x -> x
		case #Del _ -> assert ERR_gen_expecting_E (([])[0])
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

  module float (Y:numeric) : monoid with i = u8 with o = Y.t = {
    type t = #I (bool,Y.t,Y.t)
	   | #F (bool,Y.t,Y.t,Y.t)
	   | #P               -- period
	   | #M               -- minus
	   | #NE              -- neutral element
    type o = Y.t
    type i = u8.t
    def ne : t = #NE
    def op (a:t) (b:t) : t =
      match (a,b)
      case (#NE, _) -> b
      case (_, #NE) -> a
      case (#I(s1,x,b1), #I(s2,y,b2)) ->
	assert (s2 == false) (#I(Y.((s1, x * b2 + y, b1 * b2))))
      case (#I(s1,x,b1), #F(s2,y,b2,f2)) ->
	assert (s2 == false) (#F(Y.((s1, x * b2 + y, b1 * b2, f2))))
      case (#F(s1,x,b1,f1), #I(s2,y,b2)) ->
	assert (s2 == false) (#F(Y.((s1, x + y * f1, b1, f1 / b2))))
      case (#I(s,x,b), #P) -> #F(Y.((s, x, b, u8 1 / u8 10)))
      case (#P, #I(s,x,b)) ->
	assert (s == false) (#F(Y.((false, x / b, u8 1, u8 1 / b))))
      case (#M, #I(s,x,b)) ->
	assert (s == false) (#I(true,x,b))
      case (#M, #F(s,x,b,f)) ->
	assert (s == false) (#F(true,x,b,f))
      case (#M, #P) -> #F(Y.((true, u8 0, u8 1, u8 1 / u8 10)))
      case (#F _, #P) -> assert ERR_op_F_and_P_do_not_reduce (([])[0])
      case (#P, #F _) -> assert ERR_op_P_and_PF_do_not_reduce (([])[0])
      case (#P, #P) -> assert ERR_op_P_and_PF_do_not_reduce (([])[0])
      case (#F _, #F _) -> assert ERR_op_F_and_F_do_not_reduce (([])[0])
      case (#P, #M) -> assert ERR_op_PIFM_and_M_do_not_reduce (([])[0])
      case (#I _, #M) -> assert ERR_op_PIFM_and_M_do_not_reduce (([])[0])
      case (#F _, #M) -> assert ERR_op_PIFM_and_M_do_not_reduce (([])[0])
      case (#M, #M) -> assert ERR_op_PIFM_and_M_do_not_reduce (([])[0])
    def obs (x:t) : o =
      match x
      case #I(s,x,_) -> if s then Y.neg x else x
      case #F(s,x,_,_) -> if s then Y.neg x else x
      case #NE -> assert ERR_obs_expecting_I_or_F_got_NE (([])[0])
      case #P -> assert ERR_obs_expecting_I_or_F_got_P (([])[0])
      case #M -> assert ERR_obs_expecting_I_or_F_got_M (([])[0])
    def gen (x:i) : t =
      if x == '.' then #P
      else if x == '-' then #M
      else #I(Y.((false, u8 x - u8 '0', u8 10)))
  }

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

}
