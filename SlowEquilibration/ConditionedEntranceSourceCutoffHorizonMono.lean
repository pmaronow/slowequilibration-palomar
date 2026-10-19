-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceCutoffFibre

/-! The actual physical source cutoff cap-hit probability increases with
the observation horizon, at each original disorder and spherical axis. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem sourceCapHitFibre_mono_horizon {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H H' : ℝ≥0) (hHH' : H ≤ H')
    (p : SourceParameters N μ) (hp : OnSphere p.2.1) (x : Vector N) :
    sourceCapHitFibre μ Q hQ hnp α χ hχ β H (p,x) ≤
      sourceCapHitFibre μ Q hQ hnp α χ hχ β H' (p,x) := by
  rw [sourceCapHitFibre_eq_actual hN μ hnp Q hQ hQ1 α hα χ hχ β H p hp x,
    sourceCapHitFibre_eq_actual hN μ hnp Q hQ hQ1 α hα χ hχ β H' p hp x]
  have hfinite : (VectorBrownian.law N) {ω | ∃ t : ℝ≥0, t ≤ H' ∧
      α/2 ≤ |SphericalOverlapExponential.overlapValue p.2.1
        (SmoothKilled.process
          (SmoothKilled.SourceData.atSourceParameters hN μ hnp Q hQ hQ1
            α hα χ hχ p hp) β x t ω)|} ≠ ⊤ := measure_ne_top _ _
  refine measureReal_mono ?_ hfinite
  rintro ω ⟨t,ht,ha⟩
  exact ⟨t,ht.trans hHH',ha⟩

theorem sourceCapHitProbability_mono_horizon {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H H' : ℝ≥0) (hHH' : H ≤ H')
    (p : SourceParameters N μ) (hp : OnSphere p.2.1) :
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H p ≤
      sourceCapHitProbability μ Q hQ hnp α χ hχ β H' p := by
  rw [sourceCapHitProbability_eq_integral_fibre,
    sourceCapHitProbability_eq_integral_fibre]
  have hi (T : ℝ≥0) : Integrable
      (fun x => sourceCapHitFibre μ Q hQ hnp α χ hχ β T (p,x))
      (sphereLaw N) := by
    apply Integrable.of_bound
      ((sourceCapHitFibre_measurable μ Q hQ hnp α χ hχ β T).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    apply ae_of_all
    intro x
    change |sourceCapHitFibre μ Q hQ hnp α χ hχ β T (p,x)| ≤ 1
    rw [abs_of_nonneg
      (sourceCapHitFibre_mem_unit μ Q hQ hnp α χ hχ β T (p,x)).1]
    exact (sourceCapHitFibre_mem_unit μ Q hQ hnp α χ hχ β T (p,x)).2
  exact integral_mono (hi H) (hi H')
    (sourceCapHitFibre_mono_horizon hN μ hnp Q hQ hQ1 α hα χ hχ β H H' hHH' p hp)

end SlowEquilibration.ConditionedEntrance
