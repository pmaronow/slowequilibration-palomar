-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceFirstTestIdentity
public import SlowEquilibration.ConditionedEntranceSourceReferenceBounds
public import SlowEquilibration.ConditionedEntranceSmoothKilledBounds
public import SlowEquilibration.SphericalUniformStartEntropy

/-! The source-pairing identity for the actual reference and killed
resolvents. We keep the positive reference `1+f`, which avoids a separate
constant test and is sufficient for the physical initial-law estimate. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {N : ℕ}

theorem rateLaplace_reference_positive_source_identity
    (D : SourceData N) (β : ℝ) (hβ : 0≤β)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0≤κ x)
    (K : ℝ≥0) (hK : ∀ x, ‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (hJ : D.disorder∈regularDisorder) :
    let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    let H₀ := D.baseData.hamiltonian
    let H := D.hamiltonian
    let π := gibbsLaw N β H
    let w := gibbsEnergyDifference β β H₀ H
    let I := fun x => 1+uniformInitialDensity N β H₀ x
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β H₀
      D.baseData.hamiltonian_contDiff.continuous,
    ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β H
      D.hamiltonian_contDiff.continuous,
      F₁.val.fst=ᵐ[π] F ∧
      sphericalEnergyL2Map D.dimension_ge_one β H
        D.hamiltonian_contDiff.continuous u=h ∧
      (θ : ℝ)*(∫ x,I x*u.val.fst x ∂π)=
        (∫ x,κ x*F₁.val.fst x*(1-u.val.fst x) ∂π)+
        (θ : ℝ)*(∫ x,tiltDefect w x*
          (I x-F₁.val.fst x)*u.val.fst x ∂π)-
        sphericalTiltGradientPairing D.dimension_ge_one β β H₀ H
          D.baseData.hamiltonian_contDiff.continuous
          D.hamiltonian_contDiff.continuous F₀ u := by
  dsimp only
  let H₀ := D.baseData.hamiltonian
  let H := D.hamiltonian
  let π := gibbsLaw N β H
  let w := gibbsEnergyDifference β β H₀ H
  let I : Vector N→ℝ := fun x => 1+uniformInitialDensity N β H₀ x
  obtain ⟨U,F₀,F₁,u,hU,hgen,hF₀,hF₁,hu,hfirst⟩ :=
    rateLaplace_reference_first_test_identity D β κ hκ hκ0 K hK θ hθ
  let T : Vector N→ℝ := F₁.val.fst
  let v : Vector N→ℝ := u.val.fst
  let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ))
  have hC : 0≤C := by positivity
  have hT : ∀ᵐ x ∂π,‖T x‖≤C := by
    filter_upwards [hF₁,referenceRate_source_regular_bounds D β hβ θ hθ hJ]
      with x hx hb
    change T x=_ at hx
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (by linarith [hb.1])]
    exact hb.2
  have hI : ∀ᵐ x ∂π,‖I x‖≤C := by
    filter_upwards [referenceInitial_source_regular_bounds D β hβ hJ] with x hb
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hb.1])]
    exact hb.2
  have hv : ∀ᵐ x ∂π,‖v x‖≤1 := by
    filter_upwards [rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ] with x hb
    have hvfun : v=rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) :=
      congrArg (fun z : Lp ℝ 2 π => (z : Vector N→ℝ)) hu
    have hvx : v x=rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) x :=
      congrFun hvfun x
    rw [hvx,Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2
  have hTv : ∀ᵐ x ∂π,‖T x*v x‖≤C := by
    filter_upwards [hT,hv] with x hx hy
    rw [norm_mul]
    exact (mul_le_mul hx hy (norm_nonneg _) hC).trans_eq (mul_one C)
  have hIv : ∀ᵐ x ∂π,‖I x*v x‖≤C := by
    filter_upwards [hI,hv] with x hx hy
    rw [norm_mul]
    exact (mul_le_mul hx hy (norm_nonneg _) hC).trans_eq (mul_one C)
  have hDv : ∀ᵐ x ∂π,‖(I x-T x)*v x‖≤2*C := by
    filter_upwards [hI,hT,hv] with x hi ht hy
    rw [norm_mul]
    have hd : ‖I x-T x‖≤2*C := (norm_sub_le _ _).trans (by linarith)
    exact (mul_le_mul hd hy (norm_nonneg _) (by linarith)).trans_eq (mul_one _)
  have hIc : Continuous I :=
    continuous_const.add (uniformInitialDensity_continuous β H₀
      D.baseData.hamiltonian_contDiff.continuous)
  have hw : Continuous w :=
    (D.hamiltonian_contDiff.continuous.const_mul β).sub
      (D.baseData.hamiltonian_contDiff.continuous.const_mul β)
  have hk : Continuous (tiltDefect w) := by
    unfold tiltDefect
    fun_prop
  have he : Continuous (fun x => Real.exp (-w x)) := by fun_prop
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have hTi : Integrable T π :=
    Integrable.of_bound (Lp.aestronglyMeasurable F₁.val.fst) C hT
  have hTvi : Integrable (fun x => T x*v x) π :=
    Integrable.of_bound (Lp.aestronglyMeasurable F₁.val.fst |>.mul
      (Lp.aestronglyMeasurable u.val.fst)) C hTv
  have hIvi : Integrable (fun x => I x*v x) π :=
    Integrable.of_bound (hIc.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u.val.fst)) C hIv
  have hDvi : Integrable (fun x => (I x-T x)*v x) π :=
    Integrable.of_bound ((hIc.aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable F₁.val.fst)).mul
      (Lp.aestronglyMeasurable u.val.fst)) (2*C) hDv
  have hκTi : Integrable (fun x => κ x*T x) π :=
    (integrable_gibbs_of_continuous D.dimension_ge_one β
      D.hamiltonian_contDiff.continuous hκ).mul_bdd
        (Lp.aestronglyMeasurable F₁.val.fst) hT
  have hκTvi : Integrable (fun x => κ x*(T x*v x)) π :=
    (integrable_gibbs_of_continuous D.dimension_ge_one β
      D.hamiltonian_contDiff.continuous hκ).mul_bdd
        (Lp.aestronglyMeasurable F₁.val.fst |>.mul
          (Lp.aestronglyMeasurable u.val.fst)) hTv
  have hkDvi : Integrable (fun x => tiltDefect w x*((I x-T x)*v x)) π :=
    (integrable_gibbs_of_continuous D.dimension_ge_one β
      D.hamiltonian_contDiff.continuous hk).mul_bdd
        ((hIc.aestronglyMeasurable.sub
          (Lp.aestronglyMeasurable F₁.val.fst)).mul
          (Lp.aestronglyMeasurable u.val.fst)) hDv
  have heDvi : Integrable (fun x => Real.exp (-w x)*((I x-T x)*v x)) π :=
    (integrable_gibbs_of_continuous D.dimension_ge_one β
      D.hamiltonian_contDiff.continuous he).mul_bdd
        ((hIc.aestronglyMeasurable.sub
          (Lp.aestronglyMeasurable F₁.val.fst)).mul
          (Lp.aestronglyMeasurable u.val.fst)) hDv
  have hgenae : (fun x => sphericalGenerator D.dimension_ge_one β H₀
      D.baseData.hamiltonian_contDiff.continuous U x)=ᵐ[π]
      fun x => (θ : ℝ)*(I x-T x) := by
    have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one
      β β H₀ H D.baseData.hamiltonian_contDiff.continuous).ae_le
    rw [hgen]
    filter_upwards [(Lp.coeFn_smul (θ : ℝ)
      (referenceInitialVector D.baseData β-
        referenceRate D.baseData β θ (referenceInitialVector D.baseData β))).filter_mono hAC,
      (Lp.coeFn_sub (referenceInitialVector D.baseData β)
        (referenceRate D.baseData β θ (referenceInitialVector D.baseData β))).filter_mono hAC,
      (referenceInitialVector_ae D.baseData β).filter_mono hAC,hF₁]
      with x hs hd hi hf
    change ((θ : ℝ) • (referenceInitialVector D.baseData β-
      referenceRate D.baseData β θ (referenceInitialVector D.baseData β))) x=_
    rw [hs,Pi.smul_apply,smul_eq_mul,hd,Pi.sub_apply,hi,← hf]
  have hfirst' :
      (∫ x, Real.exp (-w x)*((θ : ℝ)*(I x-T x))*v x ∂π)+
      sphericalTiltGradientPairing D.dimension_ge_one β β H₀ H
        D.baseData.hamiltonian_contDiff.continuous
        D.hamiltonian_contDiff.continuous F₀ u+
      (∫ x, ((θ : ℝ)+κ x)*v x*T x ∂π)=
      ∫ x, κ x*T x ∂π := by
    have ha : (∫ x, Real.exp (-w x)*
        (sphericalGenerator D.dimension_ge_one β H₀
          D.baseData.hamiltonian_contDiff.continuous U x)*v x ∂π)=
        ∫ x, Real.exp (-w x)*((θ : ℝ)*(I x-T x))*v x ∂π := by
      apply integral_congr_ae
      exact hgenae.mono (fun x hx => by
        have hx' : sphericalGenerator D.dimension_ge_one β H₀
            D.baseData.hamiltonian_contDiff.continuous U x =
            (θ : ℝ)*(I x-T x) := hx
        change Real.exp (-w x)*
          (sphericalGenerator D.dimension_ge_one β H₀
            D.baseData.hamiltonian_contDiff.continuous U x)*v x = _
        rw [hx'])
    rw [ha] at hfirst
    simpa only [H₀,H,π,w,T,v] using hfirst
  have hfirstIntegral :
      (∫ x, Real.exp (-w x)*((θ : ℝ)*(I x-T x))*v x ∂π)=
        (θ : ℝ)*(∫ x,I x*v x ∂π)-
        (θ : ℝ)*(∫ x,T x*v x ∂π)-
        (θ : ℝ)*(∫ x,tiltDefect w x*((I x-T x)*v x) ∂π) := by
    calc
      _ = ∫ x, ((θ : ℝ)*(I x*v x)-(θ : ℝ)*(T x*v x))-
          (θ : ℝ)*(tiltDefect w x*((I x-T x)*v x)) ∂π := by
        apply integral_congr_ae
        exact .of_forall (fun x => by
          have heq : Real.exp (-w x)=1-tiltDefect w x := by
            simp only [tiltDefect,sub_sub_cancel]
          change Real.exp (-w x)*((θ : ℝ)*(I x-T x))*v x = _
          rw [heq]
          ring)
      _ = _ := by
        have hs₁ := integral_sub (hIvi.const_mul (θ : ℝ))
          (hTvi.const_mul (θ : ℝ))
        have hs₂ := integral_sub ((hIvi.const_mul (θ : ℝ)).sub
          (hTvi.const_mul (θ : ℝ))) (hkDvi.const_mul (θ : ℝ))
        simp only [Pi.sub_apply] at hs₂
        rw [hs₁] at hs₂
        simpa only [Pi.sub_apply,integral_const_mul] using hs₂
  have hsecondIntegral :
      (∫ x, ((θ : ℝ)+κ x)*v x*T x ∂π)=
        (θ : ℝ)*(∫ x,T x*v x ∂π)+
        ∫ x,κ x*(T x*v x) ∂π := by
    calc
      _ = ∫ x, (θ : ℝ)*(T x*v x)+κ x*(T x*v x) ∂π := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := by rw [integral_add (hTvi.const_mul _) hκTvi,
        integral_const_mul]
  have hrateIntegral :
      (∫ x,κ x*T x*(1-v x) ∂π)=
        (∫ x,κ x*T x ∂π)-(∫ x,κ x*(T x*v x) ∂π) := by
    calc
      _ = ∫ x,κ x*T x-κ x*(T x*v x) ∂π := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := integral_sub hκTi hκTvi
  refine ⟨F₀,F₁,u,hF₁,hu,?_⟩
  rw [hfirstIntegral,hsecondIntegral] at hfirst'
  rw [hrateIntegral]
  have htarget : (θ : ℝ)*(∫ x,I x*v x ∂π)=
    ((∫ x,κ x*T x ∂π)-(∫ x,κ x*(T x*v x) ∂π))+
    (θ : ℝ)*(∫ x,tiltDefect w x*((I x-T x)*v x) ∂π)-
    sphericalTiltGradientPairing D.dimension_ge_one β β H₀ H
      D.baseData.hamiltonian_contDiff.continuous
      D.hamiltonian_contDiff.continuous F₀ u := by
    linarith only [hfirst']
  simpa only [I,T,v,w,H₀,H,π,mul_assoc] using htarget

end SlowEquilibration.ConditionedEntrance.SmoothKilled
