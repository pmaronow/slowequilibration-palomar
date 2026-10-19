module

public import SphericalAging.L2ObservableFamilyC2

public section

/-! Joint continuity of the first two spatial derivatives of genuine
scalar expectations along a jointly continuous L² flow and its variations. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
namespace SphericalAging.L2ObservableJointC2
open HardSphereDynamics C2ObservableDerivative CompactObservableGradient
open BoundedLpComposition L2ObservableFamilyC2
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
  (C K L M : ℝ≥0) (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
  (hL : LipschitzWith L (fderiv ℝ f)) (hM : ∀ x,‖fderiv ℝ (gradient f) x‖≤M)
  (huc : UniformContinuous (fderiv ℝ (gradient f)))
  (hugc : UniformContinuous (gradient f))
  (X : ℝ≥0 → State N → Lp (State N) 2 P)
  (hX : ∀ t,ContDiff ℝ 2 (X t))
  (hXc : Continuous (fun z : ℝ≥0 × State N => X z.1 z.2))
  (hDXc : Continuous (fun z : ℝ≥0 × State N => fderiv ℝ (X z.1) z.2))
  (hDDXc : Continuous (fun z : ℝ≥0 × State N => fderiv ℝ (fderiv ℝ (X z.1)) z.2))
  (B : ℝ≥0) (h4 : ∀ t x y,MemLp (X t y-X t x : Lp (State N) 2 P) 4 P)
  (hB : ∀ t x y,lpNorm (X t y-X t x : Lp (State N) 2 P) 4 P≤B*‖y-x‖)

include hf C K L hC hK hL hXc in
theorem value_joint_continuous :
    Continuous (fun z : ℝ≥0 × State N => observable f (X z.1 z.2)) := by
  have hc : Differentiable ℝ (observable (P := P) f) := fun U =>
    (observable_hasFDerivAt f hf C K L hC hK hL U).differentiableAt
  exact hc.continuous.comp hXc

include hf K hK hugc hXc in
theorem gradientClass_joint_continuous :
    Continuous (fun z : ℝ≥0 × State N => gradientClass f hf K hK (X z.1 z.2)) := by
  have hGb : ∀ x,‖gradient f x‖≤K := fun x => by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hK x
  exact (composition_continuous (P := P) (gradient f) hugc K hGb).comp hXc

include hf C K L hC hK hL hugc hX hXc hDXc in
theorem first_joint_continuous :
    Continuous (fun z : ℝ≥0 × State N => fderiv ℝ
      (fun x => observable f (X z.1 x)) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  have he (z : ℝ≥0 × State N) := observable_family_fderiv f hf C K L hC hK hL (X z.1)
    ((hX z.1).differentiable (by norm_num)) z.2 v
  exact ((gradientClass_joint_continuous f hf K hK hugc X hXc).inner
    (hDXc.clm_apply continuous_const)).congr (fun z => (he z).symm)

include hf C K L M hC hK hL hM huc hugc hX hXc hDXc hDDXc h4 hB in
theorem second_joint_continuous :
    Continuous (fun z : ℝ≥0 × State N => fderiv ℝ (fderiv ℝ
      (fun x => observable f (X z.1 x))) z.2) := by
  apply continuous_clm_apply.mpr
  intro δ
  apply continuous_clm_apply.mpr
  intro v
  have hG := gradientClass_joint_continuous f hf K hK hugc X hXc
  have hYδ := hDXc.clm_apply (continuous_const (y := δ))
  have hYv := hDXc.clm_apply (continuous_const (y := v))
  have hDY := (hDDXc.clm_apply (continuous_const (y := δ))).clm_apply (continuous_const (y := v))
  have hA := (BoundedLpCoefficientContinuity.action_joint_continuous
    (fderiv ℝ (gradient f)) huc M hM).comp (hXc.prodMk hYδ)
  have hh := (hA.inner (𝕜 := ℝ) hYv).add (hG.inner (𝕜 := ℝ) hDY)
  exact hh.congr (fun z => (observable_family_hessian f hf C K L M hC hK hL hM huc
    (X z.1) (hX z.1) B (h4 z.1) (hB z.1) z.2 δ v).symm)

end SphericalAging.L2ObservableJointC2
