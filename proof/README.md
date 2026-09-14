# Rocq proofs of the monoidal combinators

`Monoid.v` contains the reusable generated/observable monoid interface and
its algebraic laws, independently of the parenthesis combinators.
New combinator developments can start with
`Require Import Monoid.` without importing any nesting definitions.
`Parens.v` re-exports this interface to preserve existing unqualified imports.

The basic combinators have independent developments:

- `arith.v`: `sum` and `mul` over exact integers; `max` and `min` over
  integers extended with explicit lowest/highest sentinels. Unbounded
  integers alone cannot provide both extrema identities. `simple_is_monoid`
  also supplies the generic proof rule for other numeric instances.
- `count.v`: an exact-integer counter, its monoid laws, and `count_length`.
  Finite-width overflow and IEEE arithmetic are not modelled by these proofs.
- `all.v` and `Exists.v`: the Boolean conjunction/disjunction monoids.
- `with_gen.v` and `with_obs.v`: generation/observation composition preserves
  the summary algebra. `with_obs_try` additionally supports partial callbacks.
- `filter.v`: a rejected observation falls back to observing the neutral
  element, including any failure of that observation.
- `opt.v`: first-present selection, not pointwise payload combination.
  Its monoid theorem does not require the payload to be a monoid. Observation
  distinguishes successful absence (`Some None`) from failure (`None`).

All these monoid theorems are free of axioms and admissions.

`optone.v` models first-element selection with delimiter rejection.
Its summary is `option (option I)`: `Some None` is the neutral absence,
whereas outer `None` is absorbing failure. Empty observation also fails.
`OptOneMonoid.optone_is_monoid` requires no component assumptions.

`nestable.v` uses the shared `Nest` input type from `Parens.v` and follows
the `NE`/`M`/`V` case table with optional failure. `M Base.ne` stays distinct
from `NE`; combining an observed value with any non-neutral constructor
fails. `NestableMonoid.nestable_is_monoid` assumes `IsMonoid Base`, with no
additional observation/generator laws. Both files include behavioural lemmas
for the successful and failing cases; neither introduces axioms or admissions.

`float.v` models the corrected `float0` case table with optional failures
and exact canonical rationals (not IEEE arithmetic). `FloatMonoid.op_assoc`
proves associativity for summaries with nonzero decimal scales;
`gen_consistent`, `ne_consistent`, and `op_preserves_consistency` establish
closure of this invariant. Both identity laws hold even without the invariant.
`FloatMonoid.float_is_monoid` packages these results as
`IsMonoid consistent_float`, using the same operation on a subtype of
consistent optional summaries. The decidable invariant avoids any axiom of
proof irrelevance. Theorems require no axioms or admissions.
Regression examples cover both groupings of "1", ".", "23", appended
fractional digits, negative fractions, and failures. Exact associativity of
IEEE floating-point arithmetic is not claimed.

`decimal.v` models `decimal` and `decimal_try`, with optional summary failure,
an integer mantissa, an 18-digit limit, a sign and a fractional-digit count.
The proof datatype names the empty payload `NE`; `encode_op` proves its
correspondence to the Futhark-shaped `payload`/`form` operation on consistent
summaries. `None` for the fractional count encodes the Futhark sentinel -1.
`DecimalMonoid.futhark_decimal_is_monoid` and
`futhark_decimal_try_is_monoid` package the actual payload operation on a
consistent subtype. Theorems cover associativity, identities, generation and
consistency preservation; no axioms, admissions or proof irrelevance are used.
Mantissa and counter bounds justify the exact-arithmetic model on consistent
inputs, but this is not a compiler or bit-vector refinement proof.
Observation is parameterised by numeric conversion, division and sign handling;
the examples instantiate it with exact rationals, not IEEE results.
Regressions cover multi-digit fractions, negative values, both groupings of
"1", ".", "23", the 18-digit boundary, and rejected syntax. Unlike `float`,
this parser rejects `.23` and `12.` at observation. `decimal_try` returns
successful optional output (`Some None` for rejection), whereas `decimal`
models its assertion failure with outer `None`.

`chunk.v` follows Futhark's `A`/`C` chunk-summary representation and its
`m1_to_m2`, operation, generator, and observation. An outer `option` makes
failure during inner observation absorbing. `ChunkMonoid.chunk_is_monoid`
proves the monoid laws on all optional summaries, assuming `IsMonoid` for
both components. No totality or homomorphism assumption on observations,
and no summary consistency invariant, is required. Delimiters are
polymorphic; instantiate their type with eight-bit characters for Futhark.
Additional lemmas cover ignored and retained delimiters and boundary
observation failure.

`prod.v` defines the componentwise product and proves
`ProdMonoid.prod_is_monoid`: two monoids yield a product monoid.
Product observation succeeds exactly when both component observations
succeed. `dup.v` defines input duplication and proves
`DupMonoid.dup_is_monoid`: duplication preserves the underlying summary
algebra. `dup_prod_is_monoid` composes the two results for monoids sharing
an input type; `dup_prod_gen` shows that both receive the same input.

`nat.v` models the Futhark `nat` combinator's `(value, scale)` summary,
neutral element, operation, byte generator, and observation.
`NatMonoid.nat_is_monoid` proves the monoid laws for numeric operations
satisfying `ArithmeticLaws`, on all summary pairs. The exact-integer instance
`integer_nat_is_monoid` discharges those arithmetic assumptions and includes
multi-digit examples. This does not assert exact laws for floating-point
arithmetic or model fixed-width overflow. As in Futhark, generation subtracts
the byte value of '0' without validating that the input is a decimal digit.

`Parens.v` contains a Rocq development of the algebraic
argument for `parens`. `Parens_n.v` proves the algebraic laws for the
array-based `parens_n` representation on consistent summaries.

`MonoidalOps I O` contains the summary type, neutral element, operation,
generator, and option-valued observation, matching the generated/observable
Futhark module interface. `IsMonoid` states associativity and the identity laws
directly over this interface; there is no separate algebraic record.

In `Parens.v`, the shared `Depth` development proves the algebraic laws
for the concrete `(lo, hi, net)` composition formula. It remains available
to `Parens_n.v`, but the compact `parens` summaries do not store it.

`parens_hom.v` models the homogeneous depth-one combinator directly. Its
`A` constructor has just one summary, and combining two `A` values invokes
the base operation once. It proves associativity and both identities for
every summary whenever the base is a monoid. The embedding into heterogeneous
`parens` duplicates `A`'s payload; injectivity and operation, neutral-element,
generator and observation correspondence are proved without extra base laws.
Observation failure remains option-valued, and summary failure is absorbing.

`ParensForm` has `Failure`, `A`, `Closed`, `L`, `R`, and `B` constructors.
`parens_op` uses the same direct case table as Futhark, without an outer
option or a depth guard. `form_depth` is retained for the theorem showing
the guard is redundant. `Closed` stores only an outer summary, so the
previously unused inner field cannot differ across reduction trees.
`Failure` (Futhark's `#Fail`) is absorbing and also represents a failure
encountered when observing an inner summary. Observations remain option-valued.

`parens_is_monoid` proves `IsMonoid M1 -> IsMonoid M2 ->
IsMonoid (parens M1 M2)` on the entire carrier. No consistency invariant,
normalisation premise, or observation/generator laws are needed.
`parens_del` adds configurable delimiter classification (including ignored
delimiters) to the token-based interface, with the same monoid theorem.
`ParensRegression` checks complete-summary equality for the former
counterexample, successful observation, rejected nesting, ignored delimiters,
and observation failure. The proof audit reports no axioms or admissions.

In `Parens_n.v`, the definitions follow the Futhark names and control flow:
the replay splitting and final-step laws reuse `IndexedReplay.v`, whose
iteration laws are independent of monoids, arrays, and optional failure.
The concrete definitions remain
`regions`, `empty_regions`, `region`, `put_region`, `base`, `invalid`,
`append_region`, `append_open`, `append_close`, the two replay loops, and
`parens_n_op`. `PullArray` represents the fixed-size Futhark regions array
as a size and an indexing function. `Consistent` records its size `2*n+1`,
depth bounds, active-region bound, and neutral padding. Assertion failure is
represented by `None`.

`ParensN.parens_n_op_assoc` proves associativity for all `ConsistentOpt`
arguments, assuming only `IsMonoid M`. Its proof covers successful replay,
depth-bound failure, and observation failure under both association orders.
It does not assume a canonical input sequence or a semantic correctness
theorem. Together with consistency preservation and the two neutral-element
theorems, this establishes the monoid laws on consistent optional summaries.

`Print Assumptions ParensN.parens_n_op_assoc` reports only functional
extensionality, used for equality of the function-backed arrays; it reports
no admitted proof obligations.

## Tuple-backed Parens development

`ParensRegions.v` directly models the public `Zero` and `Succ` region
constructors. It proves their sequence interpretation, fixed capacity,
injectivity, filling, replacement, push, pop and reversal laws by induction,
plus useful derived identities. `view` is proof-only, not a runtime list.

`ParensTuple.v` defines `Make` with the actual head-active tuple layout and
source-queue replay loops; failures are `option`-valued. Its theorems include
`ne_consistent`, `ne_right_neutral`, `op_success_depth`, `combine_fits_i8`
and `counts_fit_i8`.
Metadata uses mathematical integers with proved signed-byte bounds for
consistent operands at depth <50, including rejected combinations. This
does not claim compiler verification.

`ParensTupleProof.v` completes the monoid proof for this direct implementation.
It proves correspondence with `ParensN` under reversal of the occupied
prefix: individual operations, queue setup, both replay loops, the depth
guard and final metadata update. Fixed depth envelopes maintain consistency
through the replay intermediates and ensure tuple shifts cannot discard
occupied regions. The correspondence is proved, not assumed.

The main results are `TupleProof.op_preserves_consistency`,
`TupleProof.op_associative`, `TupleProof.ne_left_neutral`,
`TupleProof.gen_consistent`, and `TupleProof.monoid_laws` (which also includes
right neutrality). They require lawful region storage and, for the monoid
laws, depth <50 and `IsMonoid M`. `Zero_laws` and `Succ_laws` establish the
storage assumption for the public inductive construction.

`TupleProof.Make_is_monoid` packages the result as
`IsMonoid M -> IsMonoid (TupleProof.Make M HS HN left right)`.
Its carrier is the subtype of consistent optional tuple summaries; operation,
generator and observation are the direct `ParensTuple` definitions with
proofs attached. `None` belongs to this carrier. This is not a claim about
arbitrary malformed internal records. No semantic correctness or canonical
input-sequence assumption is used.

`Print Assumptions TupleProof.op_associative` reports only functional
extensionality, inherited from the function-backed array proof.
`Print Assumptions TupleProof.Make_is_monoid` additionally reports proof
irrelevance, used only to equate the consistency proofs attached to equal
summaries. There are no admitted obligations or custom axioms.

There are no admitted lemmas or additional Rocq package dependencies.

Build with either:

```sh
make
```

or:

```sh
rocq compile Monoid.v
rocq compile arith.v
rocq compile with_gen.v
rocq compile with_obs.v
rocq compile filter.v
rocq compile opt.v
rocq compile optone.v
rocq compile count.v
rocq compile all.v
rocq compile Exists.v
rocq compile nat.v
rocq compile prod.v
rocq compile dup.v
rocq compile chunk.v
rocq compile float.v
rocq compile decimal.v
rocq compile Parens.v
rocq compile nestable.v
rocq compile PullArray.v
rocq compile IndexedReplay.v
rocq compile Parens_n.v
rocq compile ParensRegions.v
rocq compile ParensTuple.v
rocq compile ParensTupleProof.v
```
