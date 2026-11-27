import "parens_tuple_testing"
import "../monoidal"
module P = monoidal.Parens.Make X M R4 D
entry main (xs:[]u8) = P.obs (reduce P.op P.ne
  (map (\c -> P.gen (if c=='(' || c==')' then #Del c else #E c)) xs))
-- ==
-- input { "(" } error: .*
-- input { ")" } error: .*
-- input { "a)b(" } error: .*
-- input { "(((((a)))))" } error: .*
