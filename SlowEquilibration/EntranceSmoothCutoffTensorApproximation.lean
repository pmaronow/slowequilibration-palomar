-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.EntranceSmoothCutoffCalculus
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Constructive C¹ convergence of actual finite ordered-tensor
Hamiltonians to the literal smooth entrance cutoff field. Scalar
approximants come from the proved Weierstrass primitive construction. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceSmoothCutoffTensorApproximation
open Set MeasureTheory Filter
open SphericalModel SphericalForm ConditionedEntrance
open ConditionedEntrance.TensorPolynomial EntranceSmoothCutoffCalculus
open SphericalSmoothTensorStationarity
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def smoothCutoffField (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (Q : ℝ)
    (u G v₁ v₂ : Vector N) (Hq Kq h k : ℝ) (χ : ℝ → ℝ) (x : Vector N) : ℝ :=
  fieldOfMixture μ J x+cutoffCorrection χ χ v₁ v₂ (regressionCorrection μ Q u G Hq Kq h k) x

theorem regressionCorrection_contDiff (hN : 1 ≤ N) (μ : FiniteMixture) (Q : ℝ)
    (u G : Vector N) (Hq Kq h k : ℝ) :
    ContDiff ℝ ⊤ (regressionCorrection μ Q u G Hq Kq h k) := by
  have hdeg : 2 ≤ μ.maxDegree := μ.degree_ge_two
    (Finset.max'_mem μ.coeff.support μ.support_nonempty)
  obtain ⟨ν,D,hD⟩ := polynomial_cutoff_exists_physical_mixture hN hdeg
    (regressionCorrectionAtom μ Q u G Hq Kq h k) (0 : Vector N) 0
    (Polynomial.C 1) (Polynomial.C 1)
  have he : fieldOfMixture ν D=regressionCorrection μ Q u G Hq Kq h k := by
    rw [hD]
    funext x
    simp only [Polynomial.eval_C,one_mul]
    exact regressionCorrection_atom_sum μ Q u G Hq Kq h k x
  rw [← he]
  exact fieldOfMixture_contDiff ν D

theorem smoothCutoffField_contDiff (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (Q : ℝ) (u G v₁ v₂ : Vector N)
    (Hq Kq h k : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ) :=
  ((fieldOfMixture_contDiff μ J).of_le (by simp)).add
    (((hχ.comp (innerSL ℝ v₁).contDiff).mul (hχ.comp (innerSL ℝ v₂).contDiff)).mul
      ((regressionCorrection_contDiff hN μ Q u G Hq Kq h k).of_le (by simp)))

private theorem gradient_add_actual (f g : Vector N → ℝ) (x : Vector N)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y+g y) x=gradient f x+gradient g x := by
  exact (hf.hasFDerivAt.add hg.hasFDerivAt).hasGradientAt.gradient.trans
    ((InnerProductSpace.toDual ℝ (Vector N)).symm.map_add _ _)

/-- Every smooth entrance cutoff has concrete actual finite-mixture
approximants with uniform field bounds and vanishing actual-gradient error.
No field, gradient approximation, or stationarity oracle is a premise. -/
theorem exists_actual_tensor_approximants (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (Q : ℝ) (u G v₁ v₂ : Vector N)
    (Hq Kq h k : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    ∃ (ν : ℕ → FiniteMixture) (K : (j : ℕ) → Disorder N (ν j).maxDegree)
      (M : ℝ) (δ : ℕ → ℝ),
      (∀ j x, SphericalAging.HardSphereDynamics.OnSphere x → |fieldOfMixture (ν j) (K j) x| ≤ M) ∧
      (∀ x, SphericalAging.HardSphereDynamics.OnSphere x →
        Tendsto (fun j => fieldOfMixture (ν j) (K j) x) atTop
          (𝓝 (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ x))) ∧
      (∀ j,0 ≤ δ j) ∧
      (∀ j x,SphericalAging.HardSphereDynamics.OnSphere x →
        ‖gradient (fieldOfMixture (ν j) (K j)) x-
          gradient (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ) x‖ ≤ δ j) ∧
      Tendsto δ atTop (𝓝 0) := by
  let D := regressionCorrection μ Q u G Hq Kq h k
  have hD : ContDiff ℝ 2 D := (regressionCorrection_contDiff hN μ Q u G Hq Kq h k).of_le (by simp)
  let R : ℝ := 1+Real.sqrt (N : ℝ)*(‖v₁‖+‖v₂‖)
  have hR : 0 < R := by dsimp [R]; positivity
  have hargs (x : Vector N) (hx : SphericalAging.HardSphereDynamics.OnSphere x) :
      inner ℝ v₁ x ∈ Icc (-R) R ∧ inner ℝ v₂ x ∈ Icc (-R) R := by
    have hxn := SphericalAging.LandscapeDerivatives.sphere_norm x
      ((SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq x).mp hx)
    have h₁ := abs_real_inner_le_norm v₁ x
    have h₂ := abs_real_inner_le_norm v₂ x
    rw [hxn] at h₁ h₂
    have hs := Real.sqrt_nonneg (N : ℝ)
    have hn₁ := norm_nonneg v₁
    have hn₂ := norm_nonneg v₂
    dsimp only [R]
    constructor <;> apply abs_le.mp <;> nlinarith
  obtain ⟨M₀,hM₀⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨M₁,hM₁⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
    (hχ.of_le (by norm_num)).continuous_deriv_one.continuousOn
  let C : ℝ := max 1 (max M₀ M₁)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hχb (r : ℝ) (hr : r ∈ Icc (-R) R) : |χ r| ≤ C := by
    have hb : |χ r| ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ r hr
    exact hb.trans ((le_max_left M₀ M₁).trans (le_max_right 1 (max M₀ M₁)))
  have hχd (r : ℝ) (hr : r ∈ Icc (-R) R) : |deriv χ r| ≤ C := by
    have hb : |deriv χ r| ≤ M₁ := by simpa only [Real.norm_eq_abs] using hM₁ r hr
    exact hb.trans ((le_max_right M₀ M₁).trans (le_max_right 1 (max M₀ M₁)))
  obtain ⟨B₀,hB₀⟩ := (SphericalReversibility.physicalSphere_compact N).exists_bound_of_continuousOn hD.continuous.continuousOn
  obtain ⟨G₀,hG₀⟩ := (SphericalReversibility.physicalSphere_compact N).exists_bound_of_continuousOn
    (SphericalAging.CompactObservableGradient.gradient_contDiff_one hD).continuous.continuousOn
  obtain ⟨A₀,hA₀⟩ := (SphericalReversibility.physicalSphere_compact N).exists_bound_of_continuousOn
    (fieldOfMixture_contDiff μ J).continuous.continuousOn
  let B : ℝ := max B₀ 0
  let T : ℝ := max G₀ 0
  let A : ℝ := max A₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hT : 0 ≤ T := le_max_right _ _
  have hA : 0 ≤ A := le_max_right _ _
  have hDb (x : Vector N) (hx : SphericalAging.HardSphereDynamics.OnSphere x) : |D x| ≤ B := by
    have hb : |D x| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ x hx
    exact hb.trans (le_max_left _ _)
  have hAf (x : Vector N) (hx : SphericalAging.HardSphereDynamics.OnSphere x) :
      |fieldOfMixture μ J x| ≤ A := by
    have hb : |fieldOfMixture μ J x| ≤ A₀ := by simpa only [Real.norm_eq_abs] using hA₀ x hx
    exact hb.trans (le_max_left _ _)
  have hDg (x : Vector N) (hx : SphericalAging.HardSphereDynamics.OnSphere x) : ‖gradient D x‖ ≤ T :=
    (hG₀ x hx).trans (le_max_left _ _)
  let ε : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    exact div_le_self (by norm_num : (0 : ℝ) ≤ 1)
      (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose p hp₀ hp using (fun j => UniformC1PolynomialApproximation.exists_polynomial_C1 χ
    (hχ.of_le (by norm_num)) hR (hε j))
  choose ν K hK using (fun j => regression_polynomial_cutoff_exists_physical_mixture hN μ J Q
    u G v₁ v₂ Hq Kq h k (p j) (p j))
  have hpoly (j : ℕ) (r : ℝ) (hr : r ∈ Icc (-R) R) :
      |(p j).eval r-χ r| ≤ ε j ∧ |(p j).derivative.eval r-deriv χ r| ≤ ε j := by
    simpa only [abs_sub_comm] using hp j r hr
  have hpb (j : ℕ) (r : ℝ) (hr : r ∈ Icc (-R) R) : |(p j).eval r| ≤ C+1 := by
    have he : (p j).eval r=((p j).eval r-χ r)+χ r := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [(hpoly j r hr).1,hχb r hr,hε1 j])
  let E : ℝ := (2*C+1)*(B*(‖v₁‖+‖v₂‖)+T)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨ν,K,A+(C+1)^2*B,fun j => E*ε j,?_,?_,fun j => mul_nonneg hE (hε j).le,?_,?_⟩
  · intro j x hx
    rw [hK j]
    calc
      _ ≤ |fieldOfMixture μ J x|+|(p j).eval (inner ℝ v₁ x)*(p j).eval (inner ℝ v₂ x)*D x| := abs_add_le _ _
      _ ≤ A+(C+1)^2*B := by
        apply add_le_add (hAf x hx)
        rw [abs_mul,abs_mul,pow_two]
        exact mul_le_mul (mul_le_mul (hpb j _ (hargs x hx).1) (hpb j _ (hargs x hx).2)
          (abs_nonneg _) (by positivity)) (hDb x hx) (abs_nonneg _) (by positivity)
  · intro x hx
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _)
      (fun j => ?_) (by simpa only [mul_zero] using hεlim.const_mul ((2*C+1)*B))
    rw [hK j]
    have hb := cutoffCorrection_value_error_le χ v₁ v₂ D (p j) (p j) x hC (hε j).le (hε1 j)
      (hχb _ (hargs x hx).1) (hχb _ (hargs x hx).2)
      (hpoly j _ (hargs x hx).1).1 (hpoly j _ (hargs x hx).2).1 (hDb x hx)
    change ‖fieldOfMixture μ J x+cutoffCorrection (p j).eval (p j).eval v₁ v₂ D x-
      (fieldOfMixture μ J x+cutoffCorrection χ χ v₁ v₂ D x)‖ ≤ _
    rw [add_sub_add_left_eq_sub,Real.norm_eq_abs]
    exact hb.trans_eq (by ring)
  · intro j x hx
    rw [hK j]
    have hcd := ((hχ.comp (innerSL ℝ v₁).contDiff).mul
      (hχ.comp (innerSL ℝ v₂).contDiff)).mul hD
    have hpd' := (cutoffCorrection_hasGradientAt (p j).eval (p j).eval v₁ v₂ D x
      ((p j).hasDerivAt _).differentiableAt ((p j).hasDerivAt _).differentiableAt
      (hD.differentiable (by norm_num) x)).differentiableAt
    change ‖gradient (fun y => fieldOfMixture μ J y+cutoffCorrection (p j).eval (p j).eval v₁ v₂ D y) x-
      gradient (fun y => fieldOfMixture μ J y+cutoffCorrection χ χ v₁ v₂ D y) x‖ ≤ _
    rw [gradient_add_actual (fieldOfMixture μ J) (cutoffCorrection (p j).eval (p j).eval v₁ v₂ D)
      x ((fieldOfMixture_contDiff μ J).differentiable (by simp) x)
      hpd']
    rw [gradient_add_actual (fieldOfMixture μ J) (cutoffCorrection χ χ v₁ v₂ D)
      x ((fieldOfMixture_contDiff μ J).differentiable (by simp) x)
      (hcd.differentiable (by norm_num) x),add_sub_add_left_eq_sub]
    have hb := cutoffCorrection_gradient_error_le χ v₁ v₂ D (p j) (p j) x
      (hχ.differentiable (by norm_num)) (hD.differentiable (by norm_num) x)
      hC (hε j).le (hε1 j) (hχb _ (hargs x hx).1) (hχb _ (hargs x hx).2)
      (hχd _ (hargs x hx).1) (hχd _ (hargs x hx).2)
      (hpoly j _ (hargs x hx).1).1 (hpoly j _ (hargs x hx).2).1
      (hpoly j _ (hargs x hx).1).2 (hpoly j _ (hargs x hx).2).2 (hDb x hx) (hDg x hx)
    exact hb.trans_eq (by dsimp [E]; ring)
  · simpa only [mul_zero] using hεlim.const_mul E

end SlowEquilibration.EntranceSmoothCutoffTensorApproximation
