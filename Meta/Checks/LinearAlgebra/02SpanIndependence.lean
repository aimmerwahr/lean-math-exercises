import Exercises.LinearAlgebra.«02SpanIndependence»
import Solutions.LinearAlgebra.«02SpanIndependence»
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / SpanIndependence

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against both the
reader's own attempts in `Exercises/LinearAlgebra/02SpanIndependence.lean` (the build fails here
if a proof uses a banned lemma) and the shipped canonical proofs in
`Solutions/LinearAlgebra/02SpanIndependence.lean` (a permanent regression guard).
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q2_span_universal [Submodule.span_le]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q3_span_mono [Submodule.span_mono]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q4_span_idempotent [Submodule.span_eq]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q6_singleton_independent
  [linearIndependent_unique_iff]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q7_independent_comp [LinearIndependent.comp]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q8_dependent_mem_span
  [linearIndependent_iff_notMem_span]
assert_not_uses Exercises.LinearAlgebra.SpanIndependence.q9_polynomials_independent
  [Polynomial.basisMonomials]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q2_span_universal [Submodule.span_le]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q3_span_mono [Submodule.span_mono]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q4_span_idempotent [Submodule.span_eq]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q6_singleton_independent
  [linearIndependent_unique_iff]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q7_independent_comp [LinearIndependent.comp]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q8_dependent_mem_span
  [linearIndependent_iff_notMem_span]
assert_not_uses Solutions.LinearAlgebra.SpanIndependence.q9_polynomials_independent
  [Polynomial.basisMonomials]
