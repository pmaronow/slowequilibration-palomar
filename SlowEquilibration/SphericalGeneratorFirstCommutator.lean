-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneratorGibbsCommutator
public import SlowEquilibration.SphericalGibbsEquivalentMeasures

/-! Actual first-test Gibbs commutator in completed coordinate gradients.
The cross-Gibbs test domain and its normalized gradients are constructed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def sphericalTiltGradientPairing (hN : 1≤N) (β₀ β₁ : ℝ) (H₀ H₁ : Vector N→ℝ)
    (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (F : sphericalSobolevGraph hN β₀ H₀ hH₀) (u : sphericalSobolevGraph hN β₁ H₁ hH₁) : ℝ :=
  ∫ x,tiltDefect (gibbsEnergyDifference β₀ β₁ H₀ H₁) x*
    (∑ ij : Fin N×Fin N,F.val.snd ij x*u.val.snd ij x) ∂gibbsLaw N β₁ H₁

theorem sphericalGenerator_first_commutator (hN : 1≤N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N→ℝ) (hH₀ : ContDiff ℝ 1 H₀) (hH₁ : ContDiff ℝ 1 H₁)
    (U : (sphericalGenerator hN β₀ H₀ hH₀.continuous).domain)
    (u : sphericalSobolevGraph hN β₁ H₁ hH₁.continuous) :
    ∃ F₀ : sphericalSobolevGraph hN β₀ H₀ hH₀.continuous,
      ∃ F₁ : sphericalSobolevGraph hN β₁ H₁ hH₁.continuous,
        sphericalEnergyL2Map hN β₀ H₀ hH₀.continuous F₀=U.val ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] U.val) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] F₀.val.snd ij) ∧
        sphericalCompletedDirichlet hN β₁ H₁ hH₁.continuous F₁ u=
          (∫ x,Real.exp (-gibbsEnergyDifference β₀ β₁ H₀ H₁ x)*
            (sphericalGenerator hN β₀ H₀ hH₀.continuous U x)*u.val.fst x ∂gibbsLaw N β₁ H₁)+
          sphericalTiltGradientPairing hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀ u := by
  obtain ⟨u₀,hu₀,hGu₀⟩ := sphericalSobolevGraph_changeGibbs hN β₁ β₀ H₁ H₀ hH₁.continuous hH₀.continuous u
  obtain ⟨F₀,F₁,u₁,hF₀,hF₁,hu₁,hcomm⟩ := sphericalGenerator_gibbs_weak_commutator
    hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous U u₀
  have hAC := gibbsLaw_absolutelyContinuous_gibbsLaw hN β₀ β₁ H₀ H₁ hH₀.continuous
  have heu : u₁=u := sphericalSobolevGraph_eq_of_value_ae hN β₁ H₁ hH₁ u₁ u
    (hu₁.trans (hAC.ae_eq hu₀))
  rw [heu] at hcomm
  have hΓ : completedGradientPairing hN β₀ H₀ hH₀.continuous F₀ u₀=ᵐ[gibbsLaw N β₁ H₁]
      fun x => ∑ ij : Fin N×Fin N,F₀.val.snd ij x*u.val.snd ij x := by
    filter_upwards [ae_all_iff.mpr (fun ij => hAC.ae_eq (hGu₀ ij))] with x hx
    unfold completedGradientPairing
    apply Finset.sum_congr rfl
    intro ij _
    rw [hx ij]
  have hE : (∫ x,tiltDefect (gibbsEnergyDifference β₀ β₁ H₀ H₁) x*
      completedGradientPairing hN β₀ H₀ hH₀.continuous F₀ u₀ x ∂gibbsLaw N β₁ H₁)=
      sphericalTiltGradientPairing hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀ u :=
    integral_congr_ae (hΓ.mono (fun x hx => by
      change tiltDefect (gibbsEnergyDifference β₀ β₁ H₀ H₁) x*
        completedGradientPairing hN β₀ H₀ hH₀.continuous F₀ u₀ x=_
      rw [hx]))
  rw [hE] at hcomm
  obtain ⟨F₁',hF₁',hGF₁'⟩ := sphericalSobolevGraph_changeGibbs hN β₀ β₁ H₀ H₁ hH₀.continuous hH₁.continuous F₀
  have hF₀val : F₀.val.fst=U.val := hF₀
  have hF₁'' : F₁'.val.fst=ᵐ[gibbsLaw N β₁ H₁] U.val := by
    simpa only [hF₀val] using hF₁'
  have heF : F₁'=F₁ := sphericalSobolevGraph_eq_of_value_ae hN β₁ H₁ hH₁ F₁' F₁
    (hF₁''.trans hF₁.symm)
  rw [heF] at hGF₁'
  exact ⟨F₀,F₁,hF₀,hF₁,hGF₁',hcomm⟩

end SlowEquilibration.SphericalForm
