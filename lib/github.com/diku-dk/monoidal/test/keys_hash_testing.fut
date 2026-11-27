-- | ignore
import "../monoidal"
import "../monoidal_json"
module K = monoidal_json.packed_key {def pred (c:u8) = c != 255u8}
def fold (xs:[]u8) = reduce K.op K.ne (map K.gen xs)
def same (a:K.o) (b:K.o) = match (a,b)
  case (#none,#none) -> true
  case (#some x,#some y) -> Key.equal x y
  case _ -> false
-- Observation exposes every successful hash/power through abstract Key.equal;
-- all failing summaries have the same canonical encoding.
def laws (a:[]u8) (b:[]u8) (c:[]u8) =
  let x=fold a let y=fold b let z=fold c
  let l=K.op (K.op x y) z
  let r=K.op x (K.op y z)
  let all=a++b++c
  let expected=if any (==255u8) all then #none
               else #some (Key.pack all)
  in same (K.obs l) (K.obs r) &&
     same (K.obs (K.op K.ne l)) (K.obs l) &&
     same (K.obs (K.op l K.ne)) (K.obs l) &&
     same (K.obs l) expected
