-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSParisiMeasure

@[expose] public section

namespace SlowEquilibration.CSPureModels

open Set CrisantiSommers CSParisiMeasure

/-- The actual support of a positive pure monomial is its singleton degree. -/
theorem pure_support (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    (FiniteMixture.pure p hp c hc).coeff.support = {p} := by
  exact Finsupp.support_single p hc.ne'

/-- Both genuine extreme degrees of a positive pure model equal its degree. -/
theorem pure_degrees (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    (FiniteMixture.pure p hp c hc).minDegree = p ∧
      (FiniteMixture.pure p hp c hc).maxDegree = p := by
  simp [FiniteMixture.minDegree, FiniteMixture.maxDegree, pure_support]

/-- Every pure degree at least three satisfies the actual curvature window. -/
theorem pure_degree_window (p : ℕ) (hp : 3 ≤ p) (c : ℝ) (hc : 0 < c) :
    (((FiniteMixture.pure p (by omega) c hc).minDegree : ℝ) +
      (FiniteMixture.pure p (by omega) c hc).maxDegree - 5) ^ 2 <
    6 * (((FiniteMixture.pure p (by omega) c hc).minDegree : ℝ) - 2) *
      (((FiniteMixture.pure p (by omega) c hc).maxDegree : ℝ) - 2) := by
  rw [(pure_degrees p (by omega) c hc).1, (pure_degrees p (by omega) c hc).2]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [sq_nonneg ((p : ℝ) - 3)]

/-- Strict convexity of the inverse square root of the genuine pure covariance
second derivative, valid also for the odd cubic model. -/
theorem pure_inverseSqrt_strictConvexOn (p : ℕ) (hp : 3 ≤ p) (c : ℝ) (hc : 0 < c) :
    StrictConvexOn ℝ (Ioc 0 1) (InverseSqrtCalculus.inverseSqrt
      (deriv (deriv (FiniteMixture.pure p (by omega) c hc).xi))) :=
  (FiniteMixture.pure p (by omega) c hc).degree_window_strictConvexOn
    (pure_degree_window p hp c hc)

/-- The actual unique pure-model minimizer is a strict two-atom probability
law above its actual static threshold, with a nondegenerate positive contact.
This proves the structural pure-model class, without assuming explicit pure
stationarity or ground-state formulas. -/
theorem pure_canonicalMinimizer_strict_oneStep (p : ℕ) (hp : 3 ≤ p)
    (c : ℝ) (hc : 0 < c) {β : ℝ}
    (hgt : Thresholds.staticThreshold (FiniteMixture.pure p (by omega) c hc).xi < β) :
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      (canonicalMinimizer (FiniteMixture.pure p (by omega) c hc) β).law = twoAtom x Q ∧
      CSStructure.potential (FiniteMixture.pure p (by omega) c hc) β
        (canonicalMinimizer (FiniteMixture.pure p (by omega) c hc) β).law Q = 0 ∧
      deriv (CSStructure.potential (FiniteMixture.pure p (by omega) c hc) β
        (canonicalMinimizer (FiniteMixture.pure p (by omega) c hc) β).law) Q = 0 ∧
      0 < deriv (deriv (CSStructure.potential (FiniteMixture.pure p (by omega) c hc) β
        (canonicalMinimizer (FiniteMixture.pure p (by omega) c hc) β).law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q → 0 <
        CSStructure.potential (FiniteMixture.pure p (by omega) c hc) β
          (canonicalMinimizer (FiniteMixture.pure p (by omega) c hc) β).law r := by
  apply canonicalMinimizer_strict_oneStep _ _ hgt
    (pure_inverseSqrt_strictConvexOn p hp c hc)
  rw [(pure_degrees p (by omega) c hc).1]
  exact hp

/-- Below and at the static threshold the actual pure-model minimizer is
the zero atom, including every allowed even pure degree at least four. -/
theorem pure_canonicalMinimizer_replicaSymmetric_iff (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) {β : ℝ} (hβ : 0 ≤ β) :
    (canonicalMinimizer (FiniteMixture.pure p hp c hc) β).law = MeasureTheory.Measure.dirac 0 ↔
      β ≤ Thresholds.staticThreshold (FiniteMixture.pure p hp c hc).xi :=
  canonicalMinimizer_law_eq_diracZero_iff _ hβ

end SlowEquilibration.CSPureModels
