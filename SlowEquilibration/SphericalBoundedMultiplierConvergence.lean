-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledMultiplication

/-! Actual L² convergence under bounded, almost everywhere convergent
multipliers. This supplies the dominated step for completed spherical
Sobolev scalar chain rules. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalBoundedMultiplierConvergence
open ConditionedEntrance.KilledOperator SphericalAging.BoundedItoMultiplier
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem multiplication_fixed_tendsto
    (a : ℕ → X → ℝ) (b : X → ℝ)
    (ha : ∀ n,AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (K : ℝ≥0) (hKa : ∀ n,∀ᵐ x ∂μ,‖a n x‖ ≤ K) (hKb : ∀ᵐ x ∂μ,‖b x‖ ≤ K)
    (hab : ∀ᵐ x ∂μ,Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (U : Lp ℝ 2 μ) :
    Tendsto (fun n => multiplication μ (a n) (ha n) K (hKa n) U) atTop
      (𝓝 (multiplication μ b hb K hKb U)) := by
  let e : ℕ → X → ℝ := fun n x => (a n x-b x)*U x
  have hem (n : ℕ) : AEStronglyMeasurable (fun x => e n x^2) μ :=
    (((ha n).sub hb).mul (Lp.aestronglyMeasurable U)).pow 2
  have heb (n : ℕ) : ∀ᵐ x ∂μ,‖e n x^2‖ ≤ ((2*(K : ℝ))^2)*(U x)^2 := by
    filter_upwards [hKa n,hKb] with x hax hbx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖a n x-b x‖ ≤ 2*(K : ℝ) :=
      (norm_sub_le _ _).trans ((add_le_add hax hbx).trans_eq (by ring))
    have hs : (a n x-b x)^2 ≤ (2*(K : ℝ))^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*(K : ℝ))).mpr he
    dsimp only [e]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have het : ∀ᵐ x ∂μ,Tendsto (fun n => e n x^2) atTop (𝓝 0) := by
    filter_upwards [hab] with x hx
    simpa only [e,sub_self,zero_mul,zero_pow (by norm_num : (2 : ℕ)≠0)] using
      (((hx.sub_const (b x)).mul_const (U x)).pow 2)
  have hI : Tendsto (fun n => ∫ x,e n x^2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun x => ((2*(K : ℝ))^2)*(U x)^2) hem
      ((Lp.memLp U).integrable_sq.const_mul _) heb het
  let V := multiplication μ b hb K hKb U
  have hn (n : ℕ) : ‖multiplication μ (a n) (ha n) K (hKa n) U-V‖^2=∫ x,e n x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiplication_ae μ (a n) (ha n) K (hKa n) U,
      multiplication_ae μ b hb K hKb U,
      Lp.coeFn_sub (multiplication μ (a n) (ha n) K (hKa n) U) V] with x ha hb hsub
    change V x=b x*U x at hb
    simp only [hsub,Pi.sub_apply,ha,hb,RCLike.inner_apply,conj_trivial,e]
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq := hI.congr' (.of_forall (fun n => (hn n).symm))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsqrt

theorem multiplication_tendsto
    (a : ℕ → X → ℝ) (b : X → ℝ)
    (ha : ∀ n,AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (K : ℝ≥0) (hKa : ∀ n,∀ᵐ x ∂μ,‖a n x‖ ≤ K) (hKb : ∀ᵐ x ∂μ,‖b x‖ ≤ K)
    (hab : ∀ᵐ x ∂μ,Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (U : ℕ → Lp ℝ 2 μ) (V : Lp ℝ 2 μ) (hUV : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => multiplication μ (a n) (ha n) K (hKa n) (U n)) atTop
      (𝓝 (multiplication μ b hb K hKb V)) := by
  have hfixed := multiplication_fixed_tendsto a b ha hb K hKa hKb hab V
  have hz : Tendsto (fun n => (K : ℝ)*‖U n-V‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp hUV).const_mul (K : ℝ)
  have hfirst : Tendsto (fun n => multiplication μ (a n) (ha n) K (hKa n) (U n-V)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => boundedMul_norm (ha n) K (hKa n) (U n-V)) hz
  have he (n : ℕ) : multiplication μ (a n) (ha n) K (hKa n) (U n)=
      multiplication μ (a n) (ha n) K (hKa n) (U n-V)+
        multiplication μ (a n) (ha n) K (hKa n) V := by
    rw [map_sub]
    abel
  simpa only [zero_add] using
    (hfirst.add hfixed).congr' (.of_forall (fun n => (he n).symm))

end SlowEquilibration.SphericalBoundedMultiplierConvergence
