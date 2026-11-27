import "decimal_testing"
#[prop(size(8))]
entry main (codes:[]u8) = lawful (map (\c -> ['0','7','.','-','x'][i64.u8 c % 5]) codes)
-- ==
-- property: main
