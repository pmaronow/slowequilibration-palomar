-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Quantitative bounded-square expectation control by a genuine deviation
probability, and L² convergence for varying probability spaces. -/
@[expose] public section
namespace SlowEquilibration.BoundedQuadraticConvergence
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma square_integral_le_small_bad {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hX : Measurable X) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hbound : ∀ x,|X x| ≤ C) :
    Integrable (fun x=>X x^2) μ ∧
      (∫ x,X x^2 ∂μ) ≤ ε^2+C^2*μ.real {x | ε < |X x|} := by
  let B:={x | ε < |X x|}
  have hAbs : Measurable (fun x=>|X x|) := by simpa only [Real.norm_eq_abs] using hX.norm
  have hB : MeasurableSet B:=measurableSet_lt measurable_const hAbs
  have hsq (x:E) : X x^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hbound x)
  have hi : Integrable (fun x=>X x^2) μ := Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (C^2)
    (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (X x))] using hsq x))
  have hI : Integrable (B.indicator (fun _ : E=>(1:ℝ))) μ:=(integrable_const 1).indicator hB
  have hpoint (x:E) : X x^2 ≤ ε^2+C^2*B.indicator (fun _ : E=>(1:ℝ)) x := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx,mul_one]
      exact (hsq x).trans (le_add_of_nonneg_left (sq_nonneg ε))
    · rw [Set.indicator_of_notMem hx,mul_zero,add_zero]
      have hsmall : |X x| ≤ ε:=le_of_not_gt hx
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr hsmall
  refine ⟨hi,?_⟩
  have hh:=integral_mono_ae hi ((integrable_const (ε^2)).add (hI.const_mul (C^2))) (ae_of_all _ hpoint)
  change (∫ x,X x^2 ∂μ) ≤ ∫ x,ε^2+C^2*B.indicator (fun _ : E=>(1:ℝ)) x ∂μ at hh
  rw [integral_add (integrable_const _) (hI.const_mul _),integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_indicator_const 1 hB,smul_eq_mul,mul_one] at hh
  exact hh

/-- Bounded convergence in L² with genuinely varying sample spaces and
laws; the deviation probability is the only asymptotic input. -/
theorem integral_square_tendsto_zero {E : ℕ → Type*} [∀ n,MeasurableSpace (E n)]
    (μ : (n:ℕ)→Measure (E n)) [∀ n,IsProbabilityMeasure (μ n)]
    (X : (n:ℕ)→E n→ℝ) (hX : ∀ n,Measurable (X n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n x,|X n x| ≤ C)
    (hp : ∀ ε : ℝ,0 < ε → Tendsto (fun n=>(μ n).real {x | ε < |X n x|}) atTop (𝓝 0)) :
    Tendsto (fun n=>∫ x,X n x^2 ∂μ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η:=Real.sqrt (ε/2)
  have hη : 0 < η:=Real.sqrt_pos.mpr (by positivity)
  have hη2 : η^2=ε/2:=Real.sq_sqrt (by positivity)
  have ht : Tendsto (fun n=>C^2*(μ n).real {x | η < |X n x|}) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hp η hη).const_mul (C^2)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : 0 < ε/2))] with n hn
  have hupper:=(square_integral_le_small_bad (μ n) (X n) (hX n) hC hη.le (hbound n)).2
  have hnonneg : 0 ≤ ∫ x,X n x^2 ∂μ n:=integral_nonneg (fun _=>sq_nonneg _)
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  rw [hη2] at hupper
  linarith

end
end SlowEquilibration.BoundedQuadraticConvergence
