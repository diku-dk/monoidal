-- ==
-- error: .*
import "../monoidal"
import "../monoidal_json"

-- Hiding Key.t is insufficient if parser summaries expose opt u64.
module K = monoidal_json.packed_key {def pred (_:u8) = true}
entry main : K.t = #some 0u64
