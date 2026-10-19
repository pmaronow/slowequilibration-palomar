-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePurePositivePairCanonical

/-! The literal source pairing for representatives of the same physical
reference and killed resolvents, with the same completed gradients that
enter the global weighted-energy argument. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option autoImplicit false
set_option maxHeartbeats 700000
variable {N : ℕ}

theorem rateLaplace_reference_positive_source_identity_representatives
    (D D₀ : FieldData N) (β : ℝ) (hβ : 0≤β)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0≤κ x)
    (K : ℝ≥0) (hK : ∀ x, ‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (B : ℝ)
    (hB : ∀ x, OnSphere x → |D₀.hamiltonian x| ≤ B)
    (F U : Vector N→ℝ) (GF G : Fin N×Fin N→Vector N→ℝ)
    (F₀ : sphericalSobolevGraph D.dimension_ge_one β D₀.hamiltonian
      D₀.hamiltonian_contDiff.continuous)
    (u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous)
    (hF₀ : sphericalEnergyL2Map D.dimension_ge_one β D₀.hamiltonian
      D₀.hamiltonian_contDiff.continuous F₀=
        referenceRate D₀ β θ (referenceInitialVector D₀ β))
    (hu : sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous u=
        rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ))
    (hF : F=ᵐ[gibbsLaw N β D.hamiltonian]
      referenceRate D₀ β θ (referenceInitialVector D₀ β))
    (hU : U=ᵐ[gibbsLaw N β D.hamiltonian] u.val.fst)
    (hGF : ∀ ij : Fin N×Fin N,
      GF ij=ᵐ[gibbsLaw N β D.hamiltonian] F₀.val.snd ij)
    (hG : ∀ ij : Fin N×Fin N,
      G ij=ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij) :
    let H₀ := D₀.hamiltonian
    let H := D.hamiltonian
    let π := gibbsLaw N β H
    let w := gibbsEnergyDifference β β H₀ H
    let I := fun x => 1+uniformInitialDensity N β H₀ x
    (θ : ℝ)*(∫ x,I x*U x ∂π)=
      (∫ x,κ x*F x*(1-U x) ∂π)+
      (θ : ℝ)*(∫ x,tiltDefect w x*(I x-F x)*U x ∂π)-
      (∫ x,tiltDefect w x*(∑ ij : Fin N×Fin N,
        GF ij x*G ij x) ∂π) := by
  dsimp only
  let H₀ := D₀.hamiltonian
  let H := D.hamiltonian
  let π := gibbsLaw N β H
  let w := gibbsEnergyDifference β β H₀ H
  let I : Vector N→ℝ := fun x => 1+uniformInitialDensity N β H₀ x
  obtain ⟨F₀',F₁',u',hF₀',hF₁',hu',hpair⟩ :=
    rateLaplace_reference_positive_source_identity_canonical D D₀ β hβ κ hκ hκ0
      K hK θ hθ B hB
  have heF : F₀'=F₀ := sphericalEnergyL2Map_injective
    D.dimension_ge_one β H₀ (D₀.hamiltonian_contDiff.of_le (by norm_num))
      (hF₀'.trans hF₀.symm)
  have heu : u'=u := sphericalEnergyL2Map_injective
    D.dimension_ge_one β H (D.hamiltonian_contDiff.of_le (by norm_num))
      (hu'.trans hu.symm)
  rw [heF,heu] at hpair
  have hFF : F₁'.val.fst=ᵐ[π] F := hF₁'.trans hF.symm
  have hIeq : (∫ x,I x*u.val.fst x ∂π)=(∫ x,I x*U x ∂π) := by
    apply integral_congr_ae
    exact hU.symm.mono (fun x hx => by
      change I x*u.val.fst x=I x*U x
      rw [hx])
  have hRate : (∫ x,κ x*F₁'.val.fst x*(1-u.val.fst x) ∂π)=
      (∫ x,κ x*F x*(1-U x) ∂π) := by
    apply integral_congr_ae
    filter_upwards [hFF,hU] with x hf hu
    rw [hf,hu]
  have hDef : (∫ x,tiltDefect w x*(I x-F₁'.val.fst x)*u.val.fst x ∂π)=
      (∫ x,tiltDefect w x*(I x-F x)*U x ∂π) := by
    apply integral_congr_ae
    filter_upwards [hFF,hU] with x hf hu
    rw [hf,hu]
  have hCross : sphericalTiltGradientPairing D.dimension_ge_one β β H₀ H
      D₀.hamiltonian_contDiff.continuous
      D.hamiltonian_contDiff.continuous F₀ u =
      ∫ x,tiltDefect w x*(∑ ij : Fin N×Fin N,GF ij x*G ij x) ∂π := by
    unfold sphericalTiltGradientPairing
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hGF,ae_all_iff.mpr hG] with x hf hg
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [hf ij,hg ij]
  rw [hIeq,hRate,hDef,hCross] at hpair
  simpa only [H₀,H,π,w,I,mul_assoc] using hpair

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
