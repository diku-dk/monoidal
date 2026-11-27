import "keys_hash_testing"
#[prop(size(12))]
entry main ((a,b,c):([]u8,[]u8,[]u8)) = laws a b c
-- ==
-- property: main
