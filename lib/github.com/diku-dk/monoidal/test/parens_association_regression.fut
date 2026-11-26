import "../monoidal_ex"
import "reduction_testing"

module Check = ReductionTests parenthesised_sumofproducts.T

module P = parenthesised_sumofproducts.T

-- Both associations of '(' op '(' op ')' must reject at depth one.
def nested_failure (right:bool) : f64 =
  let l = P.gen '('
  let r = P.gen ')'
  let result = loop acc=P.ne for step < 2 do
    let (a,b) = if right then
        if step == 0 then (l,r) else (l,acc)
      else if step == 0 then (l,l) else (acc,r)
    in P.op a b
  in P.obs result

entry test_parenthesised_sumofproducts_association (xs:[]u8) : bool = Check.associations (==) xs

entry test_parenthesised_nested_failure_left (_:bool) = nested_failure false
entry test_parenthesised_nested_failure_right (_:bool) = nested_failure true

-- ==
-- entry: test_parenthesised_sumofproducts_association
-- input { "2*(3+4)+5" }
-- output { true }
-- input { "(1)+(2)+(3)" }
-- output { true }
-- input { "12*(34+56)+78" }
-- output { true }


-- ==
-- entry: test_parenthesised_nested_failure_left
-- input { true }
-- error:

-- ==
-- entry: test_parenthesised_nested_failure_right
-- input { true }
-- error:
