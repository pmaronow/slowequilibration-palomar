-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralKillingFormEquation

/-! The actual unperturbed physical reference resolvent preserves positivity,
bounded order intervals and mass. The positive source rate is arbitrary. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

private theorem mass_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (hA : A.IsFormalAdjoint A)
    (u one : A.domain) (θ : ℝ) (f : E) (h0 : A one=0)
    (hr : θ • (u : E)+A u=f) : θ*inner ℝ (u : E) (one : E)=inner ℝ f one := by
  have hp := congrArg (fun z : E => inner ℝ z (one : E)) hr
  rw [inner_add_left,real_inner_smul_left,hA u one,h0,inner_zero_right,add_zero] at hp
  exact hp

private theorem scaled_domain_equation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E) (u : A.domain) (θ : ℝ) (f : E)
    (hr : θ • (u : E)+boundedPerturbation A V u=f) (hV : V u=0) :
    ∃ hd : θ • (u : E) ∈ A.domain,
      A ⟨θ • (u : E),hd⟩=θ • (f-θ • (u : E)) := by
  rw [boundedPerturbation_apply,hV,add_zero] at hr
  have hA : A u=f-θ • (u : E) := eq_sub_of_add_eq' hr
  refine ⟨A.domain.smul_mem θ u.property,?_⟩
  change A (θ • u)=θ • (f-θ • (u : E))
  rw [LinearPMap.map_smul,hA]

private theorem zero_vector (D : FieldData N) (β : ℝ) :
    killingVector D β (fun _ => 0) continuous_const=0 := by
  apply Lp.ext
  filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous (fun _ => 0) continuous_const,
    Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=gibbsLaw N β D.hamiltonian)] with x hx h0
  exact hx.trans h0.symm

private theorem zero_multiplication (D : FieldData N) (β : ℝ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    killingMultiplication D β (fun _ => 0) continuous_const 0 (by simp) U=0 := by
  apply Lp.ext
  filter_upwards [multiplication_ae (gibbsLaw N β D.hamiltonian) (fun _ => 0)
      continuous_const.aestronglyMeasurable 0 (.of_forall (by simp)) U,
    Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=gibbsLaw N β D.hamiltonian)] with x hx h0
  exact (hx.trans (zero_mul _)).trans h0.symm

/-- Literal positive-rate Laplace resolvent of the original unperturbed
Brownian sphere process, scaled to preserve constants. -/
def referenceRate (D : FieldData N) (β : ℝ) (θ : ℝ≥0) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →L[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  (θ : ℝ) • rateLaplace D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ

theorem referenceRate_nonnegative (D : FieldData N) (β : ℝ) (θ : ℝ≥0)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
    (hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ U x) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ referenceRate D β θ U x := by
  filter_upwards [rateLaplace_nonneg D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ U hU,
    Lp.coeFn_smul (θ : ℝ) (rateLaplace D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ U)]
      with x hx hs
  change 0 ≤ ((θ : ℝ) • rateLaplace D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ U) x
  rw [hs]
  exact mul_nonneg θ.coe_nonneg hx

theorem referenceRate_constant (D : FieldData N) (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ) :
    referenceRate D β θ (constantVector D β)=constantVector D β := by
  have h := rateLaplace_killing_one_identity D β (fun _ => 0) continuous_const
    (fun _ => le_rfl) 0 (by simp) θ hθ
  rw [zero_vector,map_zero,add_zero] at h
  exact h

theorem referenceRate_bounds (D : FieldData N) (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) (a b : ℝ)
    (hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,a ≤ U x ∧ U x ≤ b) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,a ≤ referenceRate D β θ U x ∧ referenceRate D β θ U x ≤ b := by
  let one := constantVector D β
  have h1 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,one x=1 :=
    gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous (fun _ => 1) continuous_const
  have hl : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ (U-a • one) x := by
    filter_upwards [hU,h1,Lp.coeFn_sub U (a • one),Lp.coeFn_smul a one] with x hx h1x hsub hsm
    simp only [hsub,Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,h1x]
    change 0 ≤ U x-a*1
    linarith
  have hh : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ (b • one-U) x := by
    filter_upwards [hU,h1,Lp.coeFn_sub (b • one) U,Lp.coeFn_smul b one] with x hx h1x hsub hsm
    simp only [hsub,Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,h1x]
    change 0 ≤ b*1-U x
    linarith
  have hleft := referenceRate_nonnegative D β θ (U-a • one) hl
  have hright := referenceRate_nonnegative D β θ (b • one-U) hh
  rw [map_sub,map_smul,referenceRate_constant D β θ hθ] at hleft hright
  filter_upwards [hleft,hright,h1,Lp.coeFn_sub (referenceRate D β θ U) (a • one),
    Lp.coeFn_sub (b • one) (referenceRate D β θ U),Lp.coeFn_smul a one,Lp.coeFn_smul b one]
      with x hlx hhx h1x hsuba hsubb hsma hsmb
  change 0 ≤ (referenceRate D β θ U-a • one) x at hlx
  change 0 ≤ (b • one-referenceRate D β θ U) x at hhx
  simp only [hsuba,Pi.sub_apply,hsma,Pi.smul_apply,smul_eq_mul,h1x] at hlx
  simp only [hsubb,Pi.sub_apply,hsmb,Pi.smul_apply,smul_eq_mul,h1x] at hhx
  change 0 ≤ referenceRate D β θ U x-a*1 at hlx
  change 0 ≤ b*1-referenceRate D β θ U x at hhx
  constructor <;> linarith

theorem inner_constantVector (D : FieldData N) (β : ℝ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    inner ℝ U (constantVector D β)=∫ x,U x ∂gibbsLaw N β D.hamiltonian := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (fun _ => 1) continuous_const] with x hx
  change constantVector D β x=1 at hx
  simp only [RCLike.inner_apply,conj_trivial,hx,one_mul]

theorem referenceRate_mass (D : FieldData N) (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    (∫ x,referenceRate D β θ U x ∂gibbsLaw N β D.hamiltonian)=
      ∫ x,U x ∂gibbsLaw N β D.hamiltonian := by
  let B := generator D β (fun _ => 0) continuous_const 0 (by simp)
  let R := rateLaplace D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ U
  have hd : R∈B.domain := rateLaplace_mem_domain D β (fun _ => 0) continuous_const
    (fun _ => le_rfl) 0 (by simp) θ hθ U
  obtain ⟨h1,hB1⟩ := generator_constant D β (fun _ => 0) continuous_const 0 (by simp)
  rw [zero_vector] at hB1
  have hs := generator_selfAdjoint D β (fun _ => 0) continuous_const 0 (by simp)
  have hformal : B.IsFormalAdjoint B := by
    have hf := LinearPMap.adjoint_isFormalAdjoint (T:=B) hs.dense_domain
    rwa [show B.adjoint=B from hs] at hf
  have hp := mass_pairing B hformal ⟨R,hd⟩ ⟨constantVector D β,h1⟩ (θ : ℝ) U hB1
    (rateLaplace_resolvent D β (fun _ => 0) continuous_const (fun _ => le_rfl) 0 (by simp) θ hθ U)
  rw [← real_inner_smul_left,inner_constantVector,inner_constantVector] at hp
  exact hp

/-- The actual reference resolvent belongs to the actual unperturbed
operator domain and has its literal source generator value. -/
theorem referenceRate_generator (D : FieldData N) (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    ∃ hd : referenceRate D β θ U ∈
      (sphericalGenerator D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous).domain,
      sphericalGenerator D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
        ⟨referenceRate D β θ U,hd⟩=(θ : ℝ) • (U-referenceRate D β θ U) :=
  scaled_domain_equation
    (sphericalGenerator D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (killingMultiplication D β (fun _ => 0) continuous_const 0 (by simp))
    ⟨rateLaplace D β (fun _ => 0) continuous_const (fun _ => le_rfl) θ U,
      rateLaplace_mem_domain D β (fun _ => 0) continuous_const (fun _ => le_rfl)
        0 (by simp) θ hθ U⟩ (θ : ℝ) U
    (rateLaplace_resolvent D β (fun _ => 0) continuous_const (fun _ => le_rfl)
      0 (by simp) θ hθ U)
    (zero_multiplication D β _)

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
