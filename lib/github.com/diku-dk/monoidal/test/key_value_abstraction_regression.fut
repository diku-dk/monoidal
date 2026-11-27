-- ==
-- error: .*
import "../monoidal"
import "../monoidal_json"

-- Client code must not be able to manufacture arbitrary packed words.
entry main : Key.t = 0u64
