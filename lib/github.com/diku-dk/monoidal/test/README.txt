Regression tests
================
Keep tests small both at compilation and execution. Prefer one exported
entry point per file when a parser is large; share definitions through
*_testing.fut rather than copying them. Keep entry points after definitions.

Use explicit examples for known bugs, malformed inputs, numeric boundaries,
field defaults/duplicates, and nesting-depth boundaries. Avoid exhaustive
word enumeration and testing every partition of a complete JSON query.
The parentheses tuple tests use a small independent stack interpreter;
malformed inputs are checked by direct parser entry points expecting errors.

Bounded property tests cover decimal summaries, separated sequences, and
delim_prod associativity. These use #[prop(size(8))], generate small alphabets
from byte values, and retain Futhark's built-in shrinking. Default: 100
candidates per property. To reproduce a run:

  make test TEST_FLAGS='--seed=42 --concurrency=2 --pass-compiler-option=--Werror'

Property testing syntax:
https://futhark.readthedocs.io/en/latest/man/futhark-test.html#property-based-testing

Hash-key properties use #[prop(size(12))]. Explicit tests also cover empty
keys, invalid-character absorption, hash/power arithmetic wraparound, keys
through 4096 bytes, 300-character record fields, and schema collisions.
Key representations remain abstract; both abstraction tests attempt to
construct the actual (u32,u32) representation and must fail to typecheck.

Historical timing before the hash-key additions, on the development Mac, Futhark 0.29.1, sequential C, 27 November 2026:
73/73 test files passed, including the three example files.
All 71 runnable test processes completed in less than 0.68 seconds, including
server startup and test-driver communication. Two files expect type errors.
Median successful clean compilation: 1.22 seconds; largest: 20.86 seconds
(monoidal_ex.fut). Complete build/test with two jobs: 93.64 seconds.
These are measurements, not portable timing assertions. Full integration
examples still take longer than one second to compile.
