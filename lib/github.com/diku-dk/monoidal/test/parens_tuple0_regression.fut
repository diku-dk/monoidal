-- | ignore

import "parens_tuple_testing"
import "../monoidal"
module ArrayRef (X:{type raw type value}) (M:monoid with i = nest X.raw X.value with o = X.value) (D:{val left:u8->bool val right:u8->bool}) = {
 module N = {def n:i64 = 0}
    -- Every segment is normalised to
    --
    --   r0 ) r1 ... ) rc ( r... ( r(c+o)
    --
    -- A depth bound of n requires 2*n+1 region slots: a viable segment can
    -- contain n unmatched closing parentheses followed by n unmatched
    -- opening parentheses.  `lo`, `hi`, and `net` describe the relative
    -- parenthesis depth of the original segment.
    type regions = [1]M.t
    type t = { valid: bool, lo: i64, hi: i64, net: i64, regions: regions }

    def empty_regions () : regions = replicate 1 M.ne

    def region (rs:regions) (i:i64) : M.t = rs[i]

    def put_region (rs:regions) (i:i64) (x:M.t) : regions =
      map2 (\j y -> if j == i then x else y) (iota 1) rs

    def base (x:M.t) : t =
      { valid = true, lo = 0, hi = 0, net = 0,
        regions = put_region (empty_regions ()) 0 x }

    def invalid () : t =
      { valid = false, lo = 0, hi = 0, net = 0,
        regions = empty_regions () }
    def ne : t = base M.ne

    -- These counters are determined by the canonical depth metadata and do
    -- not need to occupy space in every summary.
    def closes (s:t) : i64 = -s.lo
    def opens (s:t) : i64 = s.net - s.lo
    def active (s:t) : i64 = closes s + opens s

    def append_region (s:t) (x:M.t) : t =
      let i = active s
      let old = region s.regions i
      in { valid = s.valid, lo = s.lo, hi = s.hi, net = s.net,
           regions = put_region s.regions i (M.op old x) }

    def append_open (s:t) : t =
      let i = active s + 1
      in { valid = s.valid, lo = i64.min s.lo s.net,
           hi = i64.max s.hi (s.net + 1),
           net = s.net + 1,
           regions = put_region s.regions i M.ne }

    def append_close (s:t) : t =
      if opens s > 0 then
        let i = active s
        let inner = region s.regions i
        let outer = region s.regions (i-1)
        let nested = M.gen (#Nested (M.obs inner))
        let rs = put_region s.regions (i-1) (M.op outer nested)
                 |> (\rs -> put_region rs i M.ne)
        in { valid = s.valid, lo = i64.min s.lo (s.net - 1),
             hi = i64.max s.hi s.net,
             net = s.net - 1,
             regions = rs }
      else
        let i = closes s + 1
        in { valid = s.valid, lo = i64.min s.lo (s.net - 1),
             hi = i64.max s.hi s.net,
             net = s.net - 1,
             regions = put_region s.regions i M.ne }

    def op (a:t) (b:t) : t =
      let lo = i64.min a.lo (a.net + b.lo)
      let hi = i64.max a.hi (a.net + b.hi)
      let net = a.net + b.net
      in if !a.valid || !b.valid || hi-lo > N.n then invalid ()
         else
           let s0 = append_region a (region b.regions 0)
           let s1 = loop s = s0 for j < closes b do
                      append_region (append_close s)
                                    (region b.regions (j+1))
           let s2 = loop s = s1 for j < opens b do
                      append_region (append_open s)
                                    (region b.regions (closes b+j+1))
           in { valid = s2.valid, lo = lo, hi = hi, net = net,
                regions = s2.regions }

    type i = del X.raw
    def gen (x:i) : t =
      match x
      case #E x -> base (M.gen (#Raw x))
      case #Del c ->
        if D.left c then
          if N.n == 0 then invalid ()
          else append_open (base M.ne)
        else if D.right c then
          if N.n == 0 then invalid ()
          else append_close (base M.ne)
        else base M.ne

    type o = X.value
    def obs (s:t) : o =
      if s.valid && s.lo >= 0 && s.hi <= N.n && s.net == 0 then
        M.obs (region s.regions 0)
      else assert false (M.obs M.ne)
  }

module R = R0
module A = ArrayRef X M D
module S = monoidal.Parens.Make X M R D
 def same (a:A.t) (s:S.t) =
   if !a.valid then true else
   let ls = replicate (A.closes a) (#Del '(')
   let rs = replicate (A.opens a) (#Del ')')
   let af xs = copy (reduce A.op A.ne (map A.gen xs))
   let sf xs = reduce S.op S.ne (map S.gen xs)
   in A.obs (A.op (A.op (af ls) a) (af rs)) ==
      S.obs (S.op (S.op (sf ls) s) (sf rs))
 def check (xs:[]i64) =
   let af ys = copy (reduce A.op A.ne (map (\x -> A.gen (token x)) ys))
   let sf ys = reduce S.op S.ne (map (\x -> S.gen (token x)) ys)
   let n=length xs
   in same (af xs) (S.op S.ne (sf xs)) && same (af xs) (S.op (sf xs) S.ne) &&
      same (af xs) (sf xs) && all (\i -> all (\j ->
     if j<i then true else
     let a=af (take i xs) let b=af (take (j-i) (drop i xs)) let c=af (drop j xs)
     let x=sf (take i xs) let y=sf (take (j-i) (drop i xs)) let z=sf (drop j xs)
     in
        same (A.op (A.op a b) c) (S.op (S.op x y) z) &&
        same (A.op a (A.op b c)) (S.op x (S.op y z))) (iota (n+1))) (iota (n+1))
 def run =
   all (\n -> all (\k -> check (map (\j -> (k >> (2*j)) & 3) (iota n)))
     (iota (1i64 << (2*n)))) (iota 6) &&
   all (\n -> check (replicate n 2 ++ [0,1] ++ replicate n 3)) (iota 8) &&
   check ([0] ++ flatten (replicate R.depth [3,1]) ++ flatten (replicate R.depth [2,0])) &&
   check [4,2,4,0,3,4]

entry main = run
-- ==
-- input { }
-- output { true }
