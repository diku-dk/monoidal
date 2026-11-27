-- | ignore

import "../monoidal"
module Test = {
  open monoidal
  module Base = {
    type t = i64
    type i = nest i64 i64
    type o = i64
    def ne = 0i64
    def op (x:t) (y:t) = x+y
    def gen (x:i) = match x case #Raw x -> x case #Nested x -> x
    def obs (x:t) = x
  }
  module Raw = {open Base type i=i64 def gen (x:i) : t = Base.gen (#Raw x)}
  module D = {def left (c:u8) = c == '(' def right (c:u8) = c == ')'}
  module H = parens_hom {type raw=i64 type value=i64} Base D
  module P = parens Raw Base D
  def embed (x:H.t) : P.t = match x
    case #Fail -> #Fail
    case #A a -> #A (a,a)
    case #Closed a -> #Closed a
    case #L (a,b) -> #L (a,b)
    case #R (a,b) -> #R (a,b)
    case #B (a,b,c) -> #B (a,b,c)
  def all f xs = reduce (&&) true (map f xs)
  def token c : H.i = if c == '(' || c == ')' then #Del c else #E 7i64
}
entry constructors (_:bool) =
  let xs : []Test.H.t = [#Fail,#A 2,#Closed 3,#L (5,7),#R (11,13),#B (17,19,23)]
  let inputs : []Test.H.i = [#E 2,#Del '(',#Del ')',#Del '?']
  in Test.all (\x -> Test.H.op Test.H.ne x == x && Test.H.op x Test.H.ne == x &&
     Test.all (\y -> Test.embed (Test.H.op x y) == Test.P.op (Test.embed x) (Test.embed y) &&
       Test.all (\z -> Test.H.op (Test.H.op x y) z == Test.H.op x (Test.H.op y z)) xs) xs) xs &&
     Test.all (\x -> Test.embed (Test.H.gen x) == Test.P.gen x) inputs

-- ==
-- entry: constructors
-- input { true }
-- output { true }
