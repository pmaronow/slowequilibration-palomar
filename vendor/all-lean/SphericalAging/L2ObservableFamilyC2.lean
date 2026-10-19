module

public import SphericalAging.BoundedLpCompositionDerivative
public import SphericalAging.BoundedLpCoefficientContinuity
public import SphericalAging.CompactObservableGradient
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

public section

/-! Genuine C² scalar expectation along finite-dimensional C² L²
families with fourth-moment increments. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
namespace SphericalAging.L2ObservableFamilyC2
open HardSphereDynamics C2ObservableDerivative CompactObservableGradient
open BoundedLpComposition BoundedLpCompositionDerivative RandomLpCoefficient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem gradientFamily_contDiff_one (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (K M : ℝ≥0) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hM : ∀ x,‖fderiv ℝ (gradient f) x‖≤M)
    (huc : UniformContinuous (fderiv ℝ (gradient f)))
    (X : State N → Lp (State N) 2 P) (hX : ContDiff ℝ 2 X)
    (B : ℝ≥0) (h4 : ∀ x y,MemLp (X y-X x : Lp (State N) 2 P) 4 P)
    (hB : ∀ x y,lpNorm (X y-X x : Lp (State N) 2 P) 4 P≤B*‖y-x‖) :
    ContDiff ℝ 1 (fun x => gradientClass f hf K hK (X x)) := by
  have hg := gradient_contDiff_one hf
  have hGb : ∀ x,‖gradient f x‖≤K := fun x => by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hK x
  let G := fun x => composition (gradient f) hg.continuous K hGb (X x)
  have hGe : G=(fun x => gradientClass f hf K hK (X x)) := rfl
  let DG := fun x => (operator
    (derivativeCoefficient (gradient f) huc.continuous M hM (X x))).comp (fderiv ℝ X x)
  have hDx := hX.continuous_fderiv (by norm_num)
  have hc : Continuous DG := by
    apply continuous_clm_apply.mpr
    intro v
    exact (BoundedLpCoefficientContinuity.action_joint_continuous (fderiv ℝ (gradient f)) huc M hM).comp
      (hX.continuous.prodMk (hDx.clm_apply continuous_const))
  have hd (x) : HasFDerivAt G (DG x) x :=
    family_hasFDerivAt (gradient f) (hg.differentiable (by norm_num)) huc K M hGb hM
      ((hX.differentiable (by norm_num)) x).hasFDerivAt B (h4 x) (hB x)
  rw [← hGe]
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨DG,hc,hd⟩

theorem observable_family_contDiff_two (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (C K L M : ℝ≥0) (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f)) (hM : ∀ x,‖fderiv ℝ (gradient f) x‖≤M)
    (huc : UniformContinuous (fderiv ℝ (gradient f)))
    (X : State N → Lp (State N) 2 P) (hX : ContDiff ℝ 2 X)
    (B : ℝ≥0) (h4 : ∀ x y,MemLp (X y-X x : Lp (State N) 2 P) 4 P)
    (hB : ∀ x y,lpNorm (X y-X x : Lp (State N) 2 P) 4 P≤B*‖y-x‖) :
    ContDiff ℝ 2 (fun x => observable f (X x)) := by
  let DF := fun x => (observableDerivative f hf K hK (X x)).comp (fderiv ℝ X x)
  have hG := gradientFamily_contDiff_one f hf K M hK hM huc X hX B h4 hB
  have hDX := hX.fderiv_right (m := 1) (by norm_num)
  have hDF : ContDiff ℝ 1 DF := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    exact hG.inner ℝ (hDX.clm_apply contDiff_const)
  apply contDiff_succ_iff_hasFDerivAt (n := 1) |>.mpr
  refine ⟨DF,hDF,?_⟩
  intro x
  exact (observable_hasFDerivAt f hf C K L hC hK hL (X x)).comp x
    ((hX.differentiable (by norm_num)) x).hasFDerivAt

theorem observable_family_fderiv (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (C K L : ℝ≥0) (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f))
    (X : State N → Lp (State N) 2 P) (hX : Differentiable ℝ X) (x v : State N) :
    fderiv ℝ (fun y => observable f (X y)) x v=
      ⟪gradientClass f hf K hK (X x),fderiv ℝ X x v⟫_ℝ := by
  have hd := (observable_hasFDerivAt f hf C K L hC hK hL (X x)).comp x (hX x).hasFDerivAt
  change HasFDerivAt (fun y => observable f (X y)) _ x at hd
  rw [hd.fderiv]
  rfl

theorem observable_family_hessian (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (C K L M : ℝ≥0) (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f)) (hM : ∀ x,‖fderiv ℝ (gradient f) x‖≤M)
    (huc : UniformContinuous (fderiv ℝ (gradient f)))
    (X : State N → Lp (State N) 2 P) (hX : ContDiff ℝ 2 X)
    (B : ℝ≥0) (h4 : ∀ x y,MemLp (X y-X x : Lp (State N) 2 P) 4 P)
    (hB : ∀ x y,lpNorm (X y-X x : Lp (State N) 2 P) 4 P≤B*‖y-x‖)
    (x δ v : State N) :
    fderiv ℝ (fderiv ℝ (fun y => observable f (X y))) x δ v=
      ⟪operator (derivativeCoefficient (gradient f) huc.continuous M hM (X x))
        (fderiv ℝ X x δ),fderiv ℝ X x v⟫_ℝ+
      ⟪gradientClass f hf K hK (X x),fderiv ℝ (fderiv ℝ X) x δ v⟫_ℝ := by
  have hF := observable_family_contDiff_two f hf C K L M hC hK hL hM huc X hX B h4 hB
  have hDX := hX.fderiv_right (m := 1) (by norm_num)
  have hg := gradient_contDiff_one hf
  have hGb : ∀ y,‖gradient f y‖≤K := fun y => by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hK y
  have hG := family_hasFDerivAt (gradient f) (hg.differentiable (by norm_num)) huc K M hGb hM
    ((hX.differentiable (by norm_num)) x).hasFDerivAt B (h4 x) (hB x)
  have hD := ((hDX.differentiable (by norm_num)) x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hh := hG.inner ℝ hD
  have he : (fun y => ⟪gradientClass f hf K hK (X y),fderiv ℝ X y v⟫_ℝ)=
      fun y => fderiv ℝ (fun z => observable f (X z)) y v :=
    funext (fun y => (observable_family_fderiv f hf C K L hC hK hL X
      (hX.differentiable (by norm_num)) y v).symm)
  change HasFDerivAt (fun y => ⟪gradientClass f hf K hK (X y),fderiv ℝ X y v⟫_ℝ) _ x at hh
  rw [he] at hh
  have hd := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have heq := congrArg (fun A : State N →L[ℝ] ℝ => A δ) (hd.unique hh)
  have hgclass : composition (gradient f) hg.continuous K hGb (X x)=gradientClass f hf K hK (X x) := rfl
  simpa [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,innerSL_apply_apply,hgclass,add_comm] using heq

end SphericalAging.L2ObservableFamilyC2
