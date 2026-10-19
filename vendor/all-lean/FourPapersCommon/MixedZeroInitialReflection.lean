module
public import FourPapersCommon.MixedZeroOverlapCurvature
public import FourPapersCommon.MixedDisorderParity

@[expose] public section

/-! The genuine mixed minimum at zero first overlap forces zero field before
reflecting the actual Hamiltonian. This includes mixtures with ξ″(0)=0. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

 theorem mixed_field_eq_zero_of_initial_overlap_zero_min {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (hq : s.q 1=0)
    (hm : s.m 0<s.m 1) (hq2 : 0<s.q 2)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) : h=0 := by
  apply (strictMono_parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) (k+1)).injective
  rw [mixed_parisiFDeriv_initial_zero_of_min ξ s h hq hm hq2 hmin,parisiFDeriv_zero_field]

universe u
 theorem mixedConstrainedPhi_initial_zero_reflection_of_min
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω:=Ω) n ξ)
    (hq : s.q 1=0) (hm : s.m 0<s.m 1) (hq2 : 0<s.q 2)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) (t v : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t v=
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t (-v) := by
  obtain rfl := mixed_field_eq_zero_of_initial_overlap_zero_min ξ s h hq hm hq2 hmin
  exact mixedConstrainedPhi_initial_zero_reflection ξ s sk hq t v

 theorem mixedConstrainedPhi_initial_zero_negative_le_of_positive
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω:=Ω) n ξ)
    (hq : s.q 1=0) (hm : s.m 0<s.m 1) (hq2 : 0<s.q 2)
    (hmin : ∀s':RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) (t v D : ℝ)
    (H : constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t (-v) ≤ D) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t v ≤ D := by
  rw [mixedConstrainedPhi_initial_zero_reflection_of_min ξ s h sk hq hm hq2 hmin]
  exact H

end FourPapersCommon
