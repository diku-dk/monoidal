-- ==
-- error: .*
import "../monoidal"
import "../monoidal_json"

-- Client code must not be able to manufacture arbitrary hash/power pairs.
entry main : Key.t = (0u32,1u32)
