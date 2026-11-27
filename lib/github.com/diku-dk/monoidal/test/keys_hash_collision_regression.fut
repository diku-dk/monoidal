import "../monoidal_json"
-- With base 131: (1+1)*131+(132+1) = (2+1)*131+(1+1).
-- These different, equal-length byte strings deliberately collide.
entry main (_:bool) = Key.equal (Key.pack [1u8,132]) (Key.pack [2u8,1])
-- ==
-- input { true } output { true }
