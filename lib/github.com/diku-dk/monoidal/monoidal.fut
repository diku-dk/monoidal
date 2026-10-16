-- | Library of composable monoids. The library allows for processing formatted
-- byte sequences using a single monoidal operation. Examples include finding
-- the maximum average of grouped floats and computing a sum of products with
-- nested parantheses of a predetermined depth. The library is heavily inspired
-- by Oleg Kiselyov's paper
-- [More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
-- and is documented in the tech report
-- [Generic Combinators for Monoid Nesting in Futhark](https://elsman.com/pdf/monoids.pdf).

-- | The option type
type opt 'a = #some a | #none

-- | Type representing a delimiter or an element value
type del 'a = #E a | #Del u8.t

-- | An ordinary input value or the result of evaluating a nested monoid.
type nest 'a 'b = #Raw a | #Nested b

-- | Numeric values with a lossless 64-bit representation (e.g. f64).
module type numeric_bits64 = {
  include numeric
  val to_bits : t -> u64
  val from_bits : u64 -> t
}

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

-- | Fixed-projection region storage for `monoidal.Parens`. A depth d has
-- 2*d+1 slots. Use Parens.Zero/Parens.Succ: custom implementations must obey
-- the shift/reversal laws, not merely this signature.
module type parens_regions = {
  type elem
  type t
  val depth : i64
  val fill : elem -> t
  val top : t -> elem
  val last : t -> elem
  val replace : t -> elem -> t
  val push : t -> elem -> t
  val pop : t -> elem -> t
  val reverse : t -> t
}

-- | Tuple-backed homogeneous nesting, for depths 0 through 49. Metadata
-- and replay counters use i8. Invalid summaries propagate to observation,
-- which asserts. Unsupported module depths generate only failure.
module type parens = {
    module Zero : (E:{type t}) -> parens_regions with elem = E.t
    module Succ : (R:parens_regions) -> parens_regions with elem = R.elem
    module Make : (X:{type raw type value})
      -> (_M:monoid with i = nest X.raw X.value with o = X.value)
      -> (_R:parens_regions with elem = _M.t)
      -> {val left:u8 -> bool val right:u8 -> bool}
      -> monoid with i = del X.raw with o = X.value
}

-- | Module type representing module combinators for composing monoids.
module type monoidal = {
  module Parens : parens

  -- | Monoid for constructing natural numbers. Initial zeros are allowed.
  module nat   : (Y:numeric) -> monoid with i = u8 with o = Y.t

  -- | Monoid for constructing floating point values. Initial zeros and trailing
  -- zeros are allowed. The format of floats is flexible. For instance, the
  -- character sequence '-.' is considered a valid float (0.0).
  module float : (Y:numeric) -> monoid with i = u8 with o = Y.t

  -- | Total variant of `float`.  Malformed or incomplete floating-point
  -- values are observed as `#none`.
  module float_try : (Y:numeric) -> monoid with i = u8 with o = opt Y.t

  -- | Signed decimal: -?[0-9]+(\.[0-9]+)?, at most 18 digits including
  -- leading zeros. Accumulates in u64, then converts and scales at observation.
  -- Rounding can differ from float. Invalid complete numbers assert.
  module decimal : (Y:numeric) -> monoid with i = u8 with o = Y.t
  -- | Total decimal parser: invalid or incomplete numbers observe as #none.
  module decimal_try : (Y:numeric) -> monoid with i = u8 with o = opt Y.t

  -- | Integrated raw-fragment/nested-value parsers. A nested value must be
  -- an entire operand: combining it with any nonempty fragment fails.
  module float_nested : (Y:numeric) -> monoid with i = nest u8 Y.t with o = Y.t
  module float_nested_try : (Y:numeric) -> monoid with i = nest u8 Y.t with o = opt Y.t
  -- | Decimal's mantissa and nested value share the same 64-bit payload.
  module decimal_nested : (Y:numeric_bits64) -> monoid with i = nest u8 Y.t with o = Y.t
  module decimal_nested_try : (Y:numeric_bits64) -> monoid with i = nest u8 Y.t with o = opt Y.t

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

  -- | Homogeneous nesting to depth one. Raw fragments share one summary.
  module parens_hom : (X:{type raw type value})
                     -> (_M:monoid with i = nest X.raw X.value with o = X.value)
                     -> {val left:u8 -> bool val right:u8 -> bool}
                     -> monoid with i = del X.raw with o = X.value


}

module monoidal = {
  module Parens = {
    -- One slot, supporting nesting depth zero.
    module Zero (E:{type t}) : parens_regions with elem=E.t = {
     type elem = E.t
     type t = elem
     def depth = 0i64
     def fill (x:elem) : t = x
     def top (x:t) = x
     def last (x:t) = x
     def replace (_:t) (x:elem) = x
     def push (_:t) (x:elem) = x
     def pop (_:t) (padding:elem) = padding
     def reverse (x:t) = x
    }

    -- Add one field at each end. This layout makes reversal and shifts
    -- structurally recursive in the module construction.
    module Succ (R:parens_regions) : parens_regions with elem=R.elem = {
     type elem = R.elem
     type t = (elem,R.t,elem)
     def depth = R.depth+1
     def fill (x:elem) : t = (x,R.fill x,x)
     def top ((a,_,_):t) = a
     def last ((_,_,z):t) = z
     def replace ((_,r,z):t) (x:elem) : t = (x,r,z)
     def push ((a,r,_):t) (x:elem) : t = (x,R.push r a,R.last r)
     def pop ((_,r,z):t) (padding:elem) : t = (R.top r,R.pop r z,padding)
     def reverse ((a,r,z):t) : t = (z,R.reverse r,a)
    }

    local
    -- For consistent inputs of depth <=49, concatenation has span <=98.
    -- Thus all arithmetic below (including the rejected result) fits in i8.
    module NarrowMetadata = {
     type t = {valid:bool,lo:i8,hi:i8,net:i8}
     def invalid : t = {valid=false,lo=0,hi=0,net=0}
     def supported (depth:i64) = 0<=depth && depth<50
     def pack (depth:i8) (lo:i8) (hi:i8) (net:i8) : t =
       if depth<0 || depth>=50 || lo < -depth || lo>0 || hi<0 || hi>depth
          || net<lo || net>hi || hi-lo>depth
       then invalid else {valid=true,lo=lo,hi=hi,net=net}
     def combine (depth:i8) (a:t) (b:t) : t =
       if !a.valid || !b.valid then invalid else
       let lo=i8.min a.lo (a.net+b.lo)
       let hi=i8.max a.hi (a.net+b.hi)
       let net=a.net+b.net
       in pack depth lo hi net
    }

    -- Inductively constructed storage; the active region is always at the top.
    module Make (X:{type raw type value})
     (M:monoid with i = nest X.raw X.value with o = X.value)
     (R:parens_regions with elem=M.t)
     (D:{val left:u8->bool val right:u8->bool})
     : monoid with i = del X.raw with o = X.value = {
     type t = {valid:bool,lo:i8,hi:i8,net:i8,regions:R.t}
     def depth : i8 = i8.i64 R.depth
     def metadata (s:t) : NarrowMetadata.t = {valid=s.valid,lo=s.lo,hi=s.hi,net=s.net}
     def empty_regions () = R.fill M.ne
     def top (r:R.t) = R.top r
     def replace (r:R.t) (x:M.t) = R.replace r x
     def push (r:R.t) (x:M.t) = R.push r x
     def pop (r:R.t) = R.pop r M.ne
     def reverse (r:R.t) = R.reverse r
     def base (x:M.t) : t =
       if NarrowMetadata.supported R.depth then
         {valid=true,lo=0,hi=0,net=0,regions=replace (empty_regions ()) x}
       else {valid=false,lo=0,hi=0,net=0,regions=empty_regions ()}
     def invalid () : t =
       {valid=false,lo=0,hi=0,net=0,regions=empty_regions ()}
     def ne : t = base M.ne
     def closes (s:t) = -s.lo
     def opens (s:t) = s.net-s.lo
     def active (s:t) = closes s + opens s

     -- Canonical r0 ) ... ) rc ( ... ( rk is stored as
     -- (rk,...,r0,ne,...,ne). Only active+1 fields are occupied.
     def append_region (s:t) (x:M.t) : t =
       {valid=s.valid,lo=s.lo,hi=s.hi,net=s.net,
        regions=replace s.regions (M.op (top s.regions) x)}
     def append_open (s:t) : t =
       -- Replay prefixes remain within the already-validated combined bounds.
       {valid=s.valid,lo=i8.min s.lo s.net,hi=i8.max s.hi (s.net+1),
        net=s.net+1,regions=push s.regions M.ne}
     def append_close (s:t) : t =
       if opens s > 0 then
         let nested=M.gen (#Nested (M.obs (top s.regions)))
         let rest=pop s.regions
         in {valid=s.valid,lo=i8.min s.lo (s.net-1),hi=i8.max s.hi s.net,
             net=s.net-1,regions=replace rest (M.op (top rest) nested)}
       else
         {valid=s.valid,lo=i8.min s.lo (s.net-1),hi=i8.max s.hi s.net,
          net=s.net-1,regions=push s.regions M.ne}

     def op (a:t) (b:t) : t =
       let m=NarrowMetadata.combine depth (metadata a) (metadata b)
       in if !m.valid then invalid () else
         -- Convert the right summary to a forward queue using only fixed
         -- projections. Reversal puts padding first; discard exactly that padding.
         let q=loop q=reverse b.regions for _j < 2*depth-active b do pop q
         let s0=append_region a (top q)
         let (s1,q1)=loop (s,q)=(s0,pop q) for _j < closes b do
           (append_region (append_close s) (top q),pop q)
         let (s2,_)=loop (s,q)=(s1,q1) for _j < opens b do
           (append_region (append_open s) (top q),pop q)
         in {valid=s2.valid,lo=m.lo,hi=m.hi,net=m.net,regions=s2.regions}
     type i = del X.raw
     type o = X.value
     def gen (x:i) : t = if !NarrowMetadata.supported R.depth then invalid () else match x
       case #E x -> base (M.gen (#Raw x))
       case #Del c -> if D.left c then
                        if R.depth==0 then invalid () else append_open (base M.ne)
                      else if D.right c then
                        if R.depth==0 then invalid () else append_close (base M.ne)
                      else base M.ne
     def obs (s:t) : o =
       if s.valid && s.lo>=0 && s.hi<=depth && s.net==0 then M.obs (top s.regions)
       else assert false (M.obs M.ne)
    }

  }


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

  module float0 (Y:numeric) (Fail:failure) = {
    -- In #F, f is 10^(-k), where k fractional digits have been consumed.
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
	if !s2 then Fail.ok (#F(Y.((s1, x + y * (f1 / b2), b1, f1 / b2))))
	else Fail.fail false #NE
      case (#I(s,x,b), #P) -> Fail.ok (#F(Y.((s, x, b, u8 1))))
      case (#P, #I(s,x,b)) ->
	if !s then Fail.ok (#F(Y.((false, x / b, u8 1, u8 1 / b))))
	else Fail.fail false #NE
      case (#M, #I(s,x,b)) ->
	if !s then Fail.ok (#I(true,x,b)) else Fail.fail false #NE
      case (#M, #F(s,x,b,f)) ->
	if !s then Fail.ok (#F(true,x,b,f)) else Fail.fail false #NE
      case (#M, #P) -> Fail.ok (#F(Y.((true, u8 0, u8 1, u8 1))))
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

  module decimal_try (Y:numeric) = {
    type payload = {negative:bool, digits:u64, ndigits:u8, frac:i8}
    type t = #Fail | #Minus | #D payload
    type i = u8
    type o = opt Y.t
    def empty : payload = {negative=false, digits=0, ndigits=0, frac = -1}
    def ne : t = #D empty
    -- A switch keeps powers as constants rather than an explicit array.
    def pow10 (n:u8) : u64 = match n
      case 0 -> 1u64
      case 1 -> 10u64
      case 2 -> 100u64
      case 3 -> 1000u64
      case 4 -> 10000u64
      case 5 -> 100000u64
      case 6 -> 1000000u64
      case 7 -> 10000000u64
      case 8 -> 100000000u64
      case 9 -> 1000000000u64
      case 10 -> 10000000000u64
      case 11 -> 100000000000u64
      case 12 -> 1000000000000u64
      case 13 -> 10000000000000u64
      case 14 -> 100000000000000u64
      case 15 -> 1000000000000000u64
      case 16 -> 10000000000000000u64
      case 17 -> 100000000000000000u64
      case 18 -> 1000000000000000000u64
      case _ -> 0u64 -- unreachable for summaries generated by this parser
    def is_empty (x:payload) = x.ndigits == 0 && x.frac == -1 && !x.negative
    def op (a:t) (b:t) : t = match (a,b)
      case (#Fail, _) -> #Fail
      case (_, #Fail) -> #Fail
      case (#D x, #D y) ->
        if is_empty x then b else if is_empty y then a else
        let n = x.ndigits + y.ndigits
        in if y.negative || n > 18 || (x.frac >= 0 && y.frac >= 0)
           then #Fail
           else #D {negative=x.negative,
                    digits=x.digits * pow10 y.ndigits + y.digits,
                    ndigits=n,
                    frac=if x.frac >= 0 then x.frac + i8.u8 y.ndigits else y.frac}
      case (#Minus, #D y) ->
        if is_empty y then a else
        if y.negative then #Fail else #D (y with negative = true)
      case (#D x, #Minus) -> if is_empty x then b else #Fail
      case _ -> #Fail
    def gen (c:i) : t =
      if c == '-' then #Minus
      else if c == '.' then #D (empty with frac = 0)
      else if c >= '0' && c <= '9'
      then #D {negative=false, digits=u64.u8 (c-'0'), ndigits=1, frac = -1}
      else #Fail
    def obs (x:t) : o = match x
      case #D d ->
        if d.ndigits == 0 || (d.frac >= 0 &&
             (d.frac == 0 || u8.i8 d.frac == d.ndigits)) then #none
        else let scale = pow10 (if d.frac < 0 then 0 else u8.i8 d.frac)
             let v = Y.(u64 d.digits / u64 scale)
             in #some (if d.negative then Y.neg v else v)
      case _ -> #none
  }

  module decimal (Y:numeric) = {
    module D = decimal_try Y
    open D
    type o = Y.t
    def obs (x:t) : o = match D.obs x
      case #some v -> v
      case #none -> assert false (Y.i8 0)
  }

  module float_nested_try (Y:numeric) = {
    module Raw = float0 Y option_failure
    type t = #Fail | #NE | #M | #P
           | #I (bool,Y.t,Y.t) | #F (bool,Y.t,Y.t,Y.t) | #V Y.t
    type i = nest u8 Y.t
    type o = opt Y.t
    def ne : t = #NE
    def lift (x:Raw.t) : t = match x
      case #none -> #Fail
      case #some #NE -> #NE
      case #some #M -> #M
      case #some #P -> #P
      case #some (#I x) -> #I x
      case #some (#F x) -> #F x
    def raw (x:t) : Raw.t = match x
      case #NE -> #some #NE
      case #M -> #some #M
      case #P -> #some #P
      case #I x -> #some (#I x)
      case #F x -> #some (#F x)
      case _ -> #none
    def op (x:t) (y:t) : t = match x
      case #Fail -> #Fail
      case #NE -> y
      case #V _ -> (match y
        case #NE -> x
        case _ -> #Fail)
      case _ -> (match y
        case #Fail -> #Fail
        case #NE -> x
        case #V _ -> #Fail
        case _ -> lift (Raw.op (raw x) (raw y)))
    def gen (x:i) : t = match x
      case #Raw c -> lift (Raw.gen c)
      case #Nested v -> #V v
    def obs (x:t) : o = match x
      case #V v -> #some v
      case _ -> Raw.obs (raw x)
  }

  module float_nested (Y:numeric) = {
    module M = float_nested_try Y
    open M
    type o = Y.t
    def obs (x:t) : o = match M.obs x
      case #some v -> v
      case #none -> assert false (Y.i8 0)
  }

  module decimal_nested_try (Y:numeric_bits64) = {
    module Raw = decimal_try Y
    -- kind: 0 empty, 1 minus, 2 raw digits/point, 3 nested value, 4 failure.
    -- payload is a mantissa OR nested-value bits, never both.
    type t = {kind:u8, payload:u64, ndigits:u8, frac:i8, negative:bool}
    type i = nest u8 Y.t
    type o = opt Y.t
    def ne : t = {kind=0, payload=0, ndigits=0, frac = -1, negative=false}
    def fail : t = ne with kind = 4
    def lift (x:Raw.t) : t = match x
      case #Fail -> fail
      case #Minus -> ne with kind = 1
      case #D d ->
        if Raw.is_empty d then ne else
        {kind=2, payload=d.digits, ndigits=d.ndigits, frac=d.frac, negative=d.negative}
    def raw (x:t) : Raw.t =
      if x.kind == 0 then Raw.ne
      else if x.kind == 1 then #Minus
      else if x.kind == 2 then
        #D {digits=x.payload, ndigits=x.ndigits, frac=x.frac, negative=x.negative}
      else #Fail
    def op (x:t) (y:t) : t =
      if x.kind == 4 || y.kind == 4 then fail
      else if x.kind == 0 then y
      else if y.kind == 0 then x
      else if x.kind == 3 || y.kind == 3 then fail
      else lift (Raw.op (raw x) (raw y))
    def gen (x:i) : t = match x
      case #Raw c -> lift (Raw.gen c)
      case #Nested v -> ne with kind = 3 with payload = Y.to_bits v
    def obs (x:t) : o =
      if x.kind == 3 then #some (Y.from_bits x.payload)
      else Raw.obs (raw x)
  }

  module decimal_nested (Y:numeric_bits64) = {
    module M = decimal_nested_try Y
    open M
    type o = Y.t
    def obs (x:t) : o = match M.obs x
      case #some v -> v
      case #none -> assert false (Y.i8 0)
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

  module parens (M1:monoid)
                (M2:monoid with i = nest M1.i M1.o)
                (X:{ val left : u8 -> bool val right : u8 -> bool }) = {
    -- Constructor tags encode the depth shape; no depth counters are stored.
    -- Closed contains a completed parenthesised region and has no inner view.
    type t = #Fail
              | #A (M1.t, M2.t)
              | #Closed M2.t
              | #L (M2.t, M1.t)
              | #R (M1.t, M2.t)
              | #B (M1.t, M2.t, M1.t)
    def ne : t = #A (M1.ne, M2.ne)
    def depth (x:t) : (i64,i64,i64) =
      match x
      case #Fail -> (0,0,0) -- Only used by the regression's shape model.
      case #A _ -> (0,0,0)
      case #Closed _ -> (0,1,0)
      case #L _ -> (0,1,1)
      case #R _ -> (-1,0,-1)
      case #B _ -> (-1,0,0)
    def close (x:M1.t) : M2.t = M2.gen (#Nested (M1.obs x))
    def combine_forms (x:t) (y:t) : t =
      match (x,y)
      case (#A (xi,xo), #A (yi,yo)) ->
        #A (M1.op xi yi, M2.op xo yo)
      case (#A (_,xo), #Closed yo) -> #Closed (M2.op xo yo)
      case (#Closed xo, #A (_,yo)) -> #Closed (M2.op xo yo)
      case (#Closed xo, #Closed yo) -> #Closed (M2.op xo yo)
      case (#Closed xo, #L (yo,yi)) -> #L (M2.op xo yo, yi)
      case (#R (xi,xo), #Closed yo) -> #R (xi, M2.op xo yo)
      case (#A (_,xo), #L (yo,yi)) -> #L (M2.op xo yo, yi)
      case (#L (xo,xi), #A (yi,_)) -> #L (xo, M1.op xi yi)
      case (#A (xi,_), #R (yi,yo)) -> #R (M1.op xi yi, yo)
      case (#R (xi,xo), #A (_,yo)) -> #R (xi, M2.op xo yo)
      case (#A (xi,_), #B (yl,yo,yr)) -> #B (M1.op xi yl, yo, yr)
      case (#B (xl,xo,xr), #A (yi,_)) -> #B (xl, xo, M1.op xr yi)
      case (#L (xo,xi), #R (yi,yo)) ->
        #Closed (M2.op xo (M2.op (close (M1.op xi yi)) yo))
      case (#R (xi,xo), #L (yo,yi)) -> #B (xi, M2.op xo yo, yi)
      case (#L (xo,xi), #B (yi,yo,yr)) ->
        #L (M2.op xo (M2.op (close (M1.op xi yi)) yo), yr)
      case (#B (xl,xo,xr), #R (yi,yo)) ->
        #R (xl, M2.op xo (M2.op (close (M1.op xr yi)) yo))
      case (#B (xl,xo,xr), #B (yl,yo,yr)) ->
        #B (xl, M2.op xo (M2.op (close (M1.op xr yl)) yo), yr)
      case _ -> #Fail
    -- Constructor dispatch also propagates #Fail; no extra option tag.
    def op (x:t) (y:t) : t = combine_forms x y
    type i = del M1.i
    def gen (x:i) : t =
      match x
      case #E x -> #A (M1.gen x, M2.gen (#Raw x))
      case #Del c ->
        if X.left c then #L (M2.ne, M1.ne)
        else if X.right c then #R (M1.ne, M2.ne)
        else ne
    type o = M2.o
    def obs (x:t) : o =
      match x
      case #A (_,x) -> M2.obs x
      case #Closed x -> M2.obs x
      case _ -> assert ERR_unbalanced_parentheses (M2.obs M2.ne)
  }

  module parens_hom (X:{type raw type value})
                    (M:monoid with i = nest X.raw X.value with o = X.value)
                    (D:{val left:u8 -> bool val right:u8 -> bool}) = {
    -- Homogeneous depth-one nesting: a raw fragment has the same inner
    -- and outer view, so #A stores and combines only one M summary.
    -- Closed contains a completed parenthesised region and has no inner view.
    type t = #Fail
              | #A M.t
              | #Closed M.t
              | #L (M.t, M.t)
              | #R (M.t, M.t)
              | #B (M.t, M.t, M.t)
    def ne : t = #A M.ne
    def close (x:M.t) : M.t = M.gen (#Nested (M.obs x))
    def combine_forms (x:t) (y:t) : t =
      match (x,y)
      case (#A x, #A y) -> #A (M.op x y)
      case (#A xo, #Closed yo) -> #Closed (M.op xo yo)
      case (#Closed xo, #A yo) -> #Closed (M.op xo yo)
      case (#Closed xo, #Closed yo) -> #Closed (M.op xo yo)
      case (#Closed xo, #L (yo,yi)) -> #L (M.op xo yo, yi)
      case (#R (xi,xo), #Closed yo) -> #R (xi, M.op xo yo)
      case (#A xo, #L (yo,yi)) -> #L (M.op xo yo, yi)
      case (#L (xo,xi), #A yi) -> #L (xo, M.op xi yi)
      case (#A xi, #R (yi,yo)) -> #R (M.op xi yi, yo)
      case (#R (xi,xo), #A yo) -> #R (xi, M.op xo yo)
      case (#A xi, #B (yl,yo,yr)) -> #B (M.op xi yl, yo, yr)
      case (#B (xl,xo,xr), #A yi) -> #B (xl, xo, M.op xr yi)
      case (#L (xo,xi), #R (yi,yo)) ->
        #Closed (M.op xo (M.op (close (M.op xi yi)) yo))
      case (#R (xi,xo), #L (yo,yi)) -> #B (xi, M.op xo yo, yi)
      case (#L (xo,xi), #B (yi,yo,yr)) ->
        #L (M.op xo (M.op (close (M.op xi yi)) yo), yr)
      case (#B (xl,xo,xr), #R (yi,yo)) ->
        #R (xl, M.op xo (M.op (close (M.op xr yi)) yo))
      case (#B (xl,xo,xr), #B (yl,yo,yr)) ->
        #B (xl, M.op xo (M.op (close (M.op xr yl)) yo), yr)
      case _ -> #Fail
    -- Constructor dispatch also propagates #Fail; no extra option tag.
    def op (x:t) (y:t) : t = combine_forms x y
    type i = del X.raw
    def gen (x:i) : t =
      match x
      case #E x -> #A (M.gen (#Raw x))
      case #Del c ->
        if D.left c then #L (M.ne, M.ne)
        else if D.right c then #R (M.ne, M.ne)
        else ne
    type o = M.o
    def obs (x:t) : o =
      match x
      case #A x -> M.obs x
      case #Closed x -> M.obs x
      case _ -> assert ERR_unbalanced_parentheses (M.obs M.ne)
  }

}
