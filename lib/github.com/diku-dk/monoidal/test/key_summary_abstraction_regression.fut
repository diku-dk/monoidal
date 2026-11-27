-- ==
-- error: .*
import "../monoidal"
import "../monoidal_json"

-- Hiding Key.t is insufficient if parser summaries expose their raw (u32,u32) representation.
module K = monoidal_json.packed_key {def pred (_:u8) = true}
entry main : K.t = (0u32,1u32)
