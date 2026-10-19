-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSCompactAttainment
public import SlowEquilibration.CSConvexity
public import SlowEquilibration.CSStructure

@[expose] public section

namespace SlowEquilibration.CSParisiMeasure

open MeasureTheory Set CrisantiSommers

/-- Existence and uniqueness of the ordinary Crisanti--Sommers minimizer for
every canonical finite covariance and every real inverse temperature. -/
theorem existsUnique_minimizer_finiteMixture (μ : FiniteMixture) (β : ℝ) :
    ∃! ζ : Admissible, ζ.IsMinimizer β μ.xi := by
  obtain ⟨ζ, hζ⟩ := CSCompactAttainment.exists_minimizer_finiteMixture μ β
  refine ⟨ζ, hζ, ?_⟩
  intro ν hν
  exact ν.minimizer_unique ζ β μ.xi
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt) hν hζ

/-- The unique actual admissible probability minimizer. Its existence is
proved by compact weak convergence and the uniform cutoff theorem. -/
noncomputable def canonicalMinimizer (μ : FiniteMixture) (β : ℝ) : Admissible :=
  Classical.choose (CSCompactAttainment.exists_minimizer_finiteMixture μ β)

theorem canonicalMinimizer_isMinimizer (μ : FiniteMixture) (β : ℝ) :
    (canonicalMinimizer μ β).IsMinimizer β μ.xi :=
  Classical.choose_spec (CSCompactAttainment.exists_minimizer_finiteMixture μ β)

/-- Any admissible global minimizer equals the canonical measure. -/
theorem eq_canonicalMinimizer_of_isMinimizer (μ : FiniteMixture) (β : ℝ)
    (ζ : Admissible) (hζ : ζ.IsMinimizer β μ.xi) : ζ = canonicalMinimizer μ β :=
  ζ.minimizer_unique (canonicalMinimizer μ β) β μ.xi
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
    hζ (canonicalMinimizer_isMinimizer μ β)

/-- The zero-overlap Dirac law as an actual admissible candidate. -/
noncomputable def diracZeroCandidate : Admissible :=
  ⟨Measure.dirac (0 : ℝ), inferInstance,
    ⟨0, CSReplicaSymmetric.diracZero_hasCutoff (by norm_num) (by norm_num)⟩⟩

@[simp] theorem diracZeroCandidate_law : diracZeroCandidate.law = Measure.dirac (0 : ℝ) := rfl

/-- Its ordinary functional value is the annealed expression. -/
theorem diracZeroCandidate_value (μ : FiniteMixture) (β : ℝ) :
    diracZeroCandidate.value β μ.xi = β ^ 2 * μ.xi 1 / 2 := by
  rw [diracZeroCandidate.value_eq β μ.xi
    (CSReplicaSymmetric.diracZero_hasCutoff (q := 0) (by norm_num) (by norm_num))]
  exact CSReplicaSymmetric.functional_diracZero μ β

/-- The admissible zero atom is a global minimizer exactly up to the actual
static threshold. Necessity uses a strictly improving ordinary competitor. -/
theorem diracZeroCandidate_isMinimizer_iff (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) :
    diracZeroCandidate.IsMinimizer β μ.xi ↔ β ≤ Thresholds.staticThreshold μ.xi := by
  rw [← CSReplicaSymmetric.diracZeroMinimal_iff_le_staticThreshold μ hβ]
  constructor
  · intro hmin ν hν q hq
    let νA : Admissible := ⟨ν, hν, ⟨q, hq⟩⟩
    have h := hmin νA
    rw [diracZeroCandidate_value, νA.value_eq β μ.xi hq] at h
    rw [CSReplicaSymmetric.functional_diracZero μ β]
    exact h
  · intro hmin ν
    rw [diracZeroCandidate_value, ν.value_eq β μ.xi ν.hasCutoff,
      ← CSReplicaSymmetric.functional_diracZero μ β]
    exact hmin ν.law inferInstance ν.cutoff ν.hasCutoff

/-- Unconditional replica-symmetric classification of the actual unique
minimizer, including the static-threshold endpoint. -/
theorem canonicalMinimizer_law_eq_diracZero_iff (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 ≤ β) :
    (canonicalMinimizer μ β).law = Measure.dirac (0 : ℝ) ↔
      β ≤ Thresholds.staticThreshold μ.xi := by
  constructor
  · intro hlaw
    by_contra hnot
    exact CSStructure.minimizer_ne_diracZero_of_gt_staticThreshold μ (lt_of_not_ge hnot)
      (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β) hlaw
  · intro hle
    have hzero := (diracZeroCandidate_isMinimizer_iff μ hβ).mpr hle
    exact (canonicalMinimizer μ β).minimizer_law_unique diracZeroCandidate β μ.xi
      (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
      (canonicalMinimizer_isMinimizer μ β) hzero

/-- The minimum of the actual variational functional, without identifying
it with a limiting Gaussian free energy. -/
noncomputable def variationalValue (μ : FiniteMixture) (β : ℝ) : ℝ :=
  (canonicalMinimizer μ β).value β μ.xi

/-- The actual variational minimum is bounded by its zero-atom candidate. -/
theorem variationalValue_le_annealed (μ : FiniteMixture) (β : ℝ) :
    variationalValue μ β ≤ β ^ 2 * μ.xi 1 / 2 := by
  have h := canonicalMinimizer_isMinimizer μ β diracZeroCandidate
  rwa [diracZeroCandidate_value] at h

/-- Above the static threshold the actual minimum is strictly below the
annealed candidate. -/
theorem variationalValue_lt_annealed_of_gt_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hgt : Thresholds.staticThreshold μ.xi < β) :
    variationalValue μ β < β ^ 2 * μ.xi 1 / 2 := by
  have hβ : 0 ≤ β := (lt_trans μ.staticThreshold_pos hgt).le
  obtain ⟨r, hr, t, ht, hp, hc, hlt⟩ :=
    CSReplicaSymmetric.exists_improving_two_atom_of_gt_staticThreshold μ hβ hgt
  let ν : Admissible := ⟨mixture (Measure.dirac (0 : ℝ)) (Measure.dirac r) t,
    hp, ⟨r, hc⟩⟩
  have hle := canonicalMinimizer_isMinimizer μ β ν
  rw [ν.value_eq β μ.xi hc] at hle
  exact hle.trans_lt hlt

/-- The true variational optimum equals its annealed candidate exactly in
the static-threshold replica-symmetric range. -/
theorem variationalValue_eq_annealed_iff (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) :
    variationalValue μ β = β ^ 2 * μ.xi 1 / 2 ↔
      β ≤ Thresholds.staticThreshold μ.xi := by
  constructor
  · intro heq
    by_contra hnot
    exact (variationalValue_lt_annealed_of_gt_staticThreshold μ
      (lt_of_not_ge hnot)).ne heq
  · intro hle
    apply le_antisymm (variationalValue_le_annealed μ β)
    exact CSReplicaSymmetric.annealed_le_functional_of_le_staticThreshold μ hβ hle
      (canonicalMinimizer μ β).law (canonicalMinimizer μ β).hasCutoff

/-- Above the static threshold the unique actual minimizer is a literal
strict one-step law with the nondegenerate contact required in the manuscript.
Minimizer existence is supplied by the proved compact-attainment theorem. -/
theorem canonicalMinimizer_strict_oneStep (μ : FiniteMixture)
    (hd : 3 ≤ μ.minDegree) {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) :
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      (canonicalMinimizer μ β).law = twoAtom x Q ∧
      CSStructure.potential μ β (canonicalMinimizer μ β).law Q = 0 ∧
      deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law) Q = 0 ∧
      0 < deriv (deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q →
        0 < CSStructure.potential μ β (canonicalMinimizer μ β).law r :=
  CSStructure.minimizer_strict_oneStep_of_gt_staticThreshold μ hd hgt
    (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β) hξ

/-- The degree-window conclusion now holds for the actual existing unique
minimizer, with no minimizer-existence or RS-classification premises. -/
theorem degree_window_canonicalMinimizer_strict_oneStep (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ} (hgt : Thresholds.staticThreshold μ.xi < β) :
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      (canonicalMinimizer μ β).law = twoAtom x Q ∧
      CSStructure.potential μ β (canonicalMinimizer μ β).law Q = 0 ∧
      deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law) Q = 0 ∧
      0 < deriv (deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q →
        0 < CSStructure.potential μ β (canonicalMinimizer μ β).law r :=
  canonicalMinimizer_strict_oneStep μ (by omega) hgt
    (μ.degree_window_strictConvexOn hwindow)

end SlowEquilibration.CSParisiMeasure
