-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneratorGibbsCommutator
public import SlowEquilibration.SphericalGibbsEquivalentMeasures
public import SlowEquilibration.SphericalSobolevSquareCrossPairing

/-! Literal square-test commutator for the source weighted cross term.
The square domain, reference test, and Gibbs form transport are derived. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def sphericalTiltGradientCross (hN : 1≤N) (β₀ β₁ : ℝ) (H₀ H₁ : Vector N→ℝ)
    (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (F : sphericalSobolevGraph hN β₀ H₀ hH₀) (u : sphericalSobolevGraph hN β₁ H₁ hH₁) : ℝ :=
  ∫ x,tiltDefect (gibbsEnergyDifference β₀ β₁ H₀ H₁) x*
    (∑ ij : Fin N×Fin N,u.val.fst x*F.val.snd ij x*u.val.snd ij x) ∂gibbsLaw N β₁ H₁

theorem sphericalGenerator_square_commutator (hN : 1≤N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N→ℝ) (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    (U : (sphericalGenerator hN β₀ H₀ hH₀.continuous).domain)
    (u : sphericalSobolevGraph hN β₁ H₁ hH₁.continuous) (CU : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β₁ H₁,‖u.val.fst x‖≤CU) :
    ∃ F₀ : sphericalSobolevGraph hN β₀ H₀ hH₀.continuous,
      ∃ F₁ : sphericalSobolevGraph hN β₁ H₁ hH₁.continuous,
        sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous F₀=U.val ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] U.val) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] F₀.val.snd ij) ∧
        sphericalWeightedGradientCross hN β₁ H₁ hH₁.continuous u F₁=
          (1/2 : ℝ)*(∫ x,Real.exp (-gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
            (sphericalGenerator hN β₀ H₀ hH₀.continuous U x)*(u.val.fst x)^2 ∂gibbsLaw N β₁ H₁)+
          sphericalTiltGradientCross hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀ u := by
  obtain ⟨F₀,hF₀,_⟩ := sphericalGenerator_domain_form hN β₀ H₀ hH₀.continuous U
  have hF₀' : F₀.val.fst=U.val := hF₀
  obtain ⟨F₁,hF₁,hGF₁⟩ := sphericalSobolevGraph_changeGibbs hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀
  have hF₁' : F₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] U.val := by simpa only [hF₀'] using hF₁
  obtain ⟨v₁,hv₁,hGv₁,hpair⟩ := sphericalSobolevGraph_square_cross_pairing hN β₁ H₁ hH₁.continuous u F₁ CU hU
  obtain ⟨v₀,hv₀,hGv₀⟩ := sphericalSobolevGraph_changeGibbs hN β₁ β₀ H₁ H₀ hH₁.continuous hH₀.continuous v₁
  have hAC := gibbsLaw_absolutelyContinuous_gibbsLaw hN β₀ β₁ H₀ H₁ hH₀.continuous
  obtain ⟨F₀',F₁',v₁',hF₀'',hF₁'',hv₁',hcomm⟩ := sphericalGenerator_gibbs_weak_commutator
    hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous U v₀
  have heF₀ : F₀'=F₀ := sphericalEnergyL2Map_injective hN β₀ H₀ hH₀ (hF₀''.trans hF₀.symm)
  have heF₁ : F₁'=F₁ := sphericalSobolevGraph_eq_of_value_ae hN β₁ H₁ hH₁ F₁' F₁ (hF₁''.trans hF₁'.symm)
  have hev₁ : v₁'=v₁ := sphericalSobolevGraph_eq_of_value_ae hN β₁ H₁ hH₁ v₁' v₁
    (hv₁'.trans (hAC.ae_eq hv₀))
  rw [heF₀,heF₁,hev₁,hpair] at hcomm
  have hI : (∫ x,Real.exp (-gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
      (sphericalGenerator hN β₀ H₀ hH₀.continuous U x)*v₁.val.fst x ∂gibbsLaw N β₁ H₁)=
      ∫ x,Real.exp (-gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
        (sphericalGenerator hN β₀ H₀ hH₀.continuous U x)*(u.val.fst x)^2 ∂gibbsLaw N β₁ H₁ := by
    apply integral_congr_ae
    filter_upwards [hv₁] with x hx
    rw [hx]
  have hgrad : ∀ ij : Fin N×Fin N,v₀.val.snd ij=ᵐ[gibbsLaw N β₁ H₁]
      fun x => 2*u.val.fst x*u.val.snd ij x := fun ij =>
    (hAC.ae_eq (hGv₀ ij)).trans (hGv₁ ij)
  have hΓ : completedGradientPairing hN β₀ H₀ hH₀.continuous F₀ v₀=ᵐ[gibbsLaw N β₁ H₁]
      fun x => 2*(∑ ij : Fin N×Fin N,u.val.fst x*F₀.val.snd ij x*u.val.snd ij x) := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    unfold completedGradientPairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [hx ij]
    ring
  have hE : (∫ x,tiltDefect (gibbsEnergyDifference β₀ β₁ H₀ H₁) x*
      completedGradientPairing hN β₀ H₀ hH₀.continuous F₀ v₀ x ∂gibbsLaw N β₁ H₁)=
      2*sphericalTiltGradientCross hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀ u := by
    rw [sphericalTiltGradientCross,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hΓ] with x hx
    rw [hx]
    ring
  rw [hI,hE] at hcomm
  refine ⟨F₀,F₁,hF₀,hF₁',hGF₁,?_⟩
  linarith

end SlowEquilibration.SphericalForm
