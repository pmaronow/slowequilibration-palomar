-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureCutoffFibre

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

theorem pureSourceCapHitFibre_mono_horizon {N : ℕ} (hN : 1 ≤ N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H H' : ℝ≥0) (hHH' : H ≤ H')
    (p : SourceParameters N (FiniteMixture.pure d hd c hc)) (hp : OnSphere p.2.1) (x : Vector N) :
    pureSourceCapHitFibre d hd c hc Q α χ hχ β H (p,x) ≤
      pureSourceCapHitFibre d hd c hc Q α χ hχ β H' (p,x) := by
  rw [pureSourceCapHitFibre_eq_actual hN d hd c hc Q α hα χ hχ β H p hp x,
    pureSourceCapHitFibre_eq_actual hN d hd c hc Q α hα χ hχ β H' p hp x]
  have hfinite : (VectorBrownian.law N) {ω | ∃ t : ℝ≥0, t ≤ H' ∧
      α/2 ≤ |SphericalOverlapExponential.overlapValue p.2.1
        (SmoothKilledGeneral.process
          (SmoothKilledGeneral.FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ) β x t ω)|} ≠ ⊤ := measure_ne_top _ _
  refine measureReal_mono ?_ hfinite
  rintro ω ⟨t,ht,ha⟩
  exact ⟨t,ht.trans hHH',ha⟩

theorem pureSourceCapHitProbability_mono_horizon {N : ℕ} (hN : 1 ≤ N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H H' : ℝ≥0) (hHH' : H ≤ H')
    (p : SourceParameters N (FiniteMixture.pure d hd c hc)) (hp : OnSphere p.2.1) :
    pureSourceCapHitProbability d hd c hc Q α χ hχ β H p ≤
      pureSourceCapHitProbability d hd c hc Q α χ hχ β H' p := by
  rw [pureSourceCapHitProbability_eq_integral_fibre,
    pureSourceCapHitProbability_eq_integral_fibre]
  have hi (T : ℝ≥0) : Integrable
      (fun x => pureSourceCapHitFibre d hd c hc Q α χ hχ β T (p,x))
      (sphereLaw N) := by
    apply Integrable.of_bound
      ((pureSourceCapHitFibre_measurable d hd c hc Q α χ hχ β T).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    apply ae_of_all
    intro x
    change |pureSourceCapHitFibre d hd c hc Q α χ hχ β T (p,x)| ≤ 1
    rw [abs_of_nonneg
      (pureSourceCapHitFibre_mem_unit d hd c hc Q α χ hχ β T (p,x)).1]
    exact (pureSourceCapHitFibre_mem_unit d hd c hc Q α χ hχ β T (p,x)).2
  exact integral_mono (hi H) (hi H')
    (pureSourceCapHitFibre_mono_horizon hN d hd c hc Q α hα χ hχ β H H' hHH' p hp)

end SlowEquilibration.ConditionedEntrance
