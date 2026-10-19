module
public import FourPapersCommon.MixedEndpointOptimality
public import FourPapersCommon.MixedGuerraConvergence
public import Targets.RSBSchemeOverlapReduction

@[expose] public section

/-! Exact removal of coincident masses and interior overlaps for the actual
mixed covariance functional and the genuine Gaussian interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedClockScheme_padZeroFirst (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) :
    mixedClockScheme ξ s.padZeroFirst = (mixedClockScheme ξ s).padZeroFirst := rfl

theorem schemeCorrection_padZeroFirst (θ : ℝ → ℝ) {k : ℕ} (s : RSBScheme k) :
    schemeCorrection θ s.padZeroFirst = schemeCorrection θ s := by
  unfold schemeCorrection
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, Finset.sum_range_succ']
  simp only [RSBScheme.padZeroFirst, Nat.zero_sub, s.m_zero, zero_mul,
    add_zero, Nat.add_sub_cancel]

theorem mixedSchemeCorrection_padZeroFirst (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) : mixedSchemeCorrection ξ s.padZeroFirst = mixedSchemeCorrection ξ s := by
  rw [mixedSchemeCorrection_eq_schemeCorrection, mixedSchemeCorrection_eq_schemeCorrection,
    schemeCorrection_padZeroFirst]

theorem mixedFunctional_padZeroFirst (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure s.padZeroFirst) =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  rw [mixedFunctional_scheme, mixedFunctional_scheme, mixedClockScheme_padZeroFirst,
    mixedSchemeCorrection_padZeroFirst]
  rw [←parisiF_dropZeroFirst (mixedClockScheme ξ s).padZeroFirst
    (mixedClockScheme ξ s).padZeroFirst_mass_one (mixedBeta ξ), RSBScheme.drop_padZeroFirst]

theorem mixedInterpolationPsi_mergeEqualMass (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1)
    (hm : s.m p = s.m (p + 1)) (h t : ℝ) :
    mixedInterpolationPsi ξ (s.mergeEqualMass p hp hm) h t = mixedInterpolationPsi ξ s h t := by
  rw [mixedInterpolationPsi, mixedInterpolationPsi, mixedClockScheme_mergeEqualMass,
    parisiF_mergeEqualMass (mixedClockScheme ξ s) p hp hm (mixedBeta ξ), mixedSchemeCorrection_eq_schemeCorrection,
    mixedSchemeCorrection_eq_schemeCorrection, schemeCorrection_mergeEqualMass]

theorem mixed_minimizer_mergeEqualMass (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1)
    (hm : s.m p = s.m (p + 1)) (h : ℝ)
    (hmin : ∀ s' : RSBScheme (k + 1), mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.mergeEqualMass p hp hm)) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s') := by
  intro s'
  rw [mixedFunctional_mergeEqualMass]
  simpa only [mixedFunctional_padZeroFirst] using hmin s'.padZeroFirst

theorem mixedInterpolationPsi_raiseMass_zero_variance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h t : ℝ) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Icc (s.m p) (s.m (p + 1))) (hq : s.q (p + 1) = s.q p) :
    mixedInterpolationPsi ξ (s.raiseMass p hp0 hp m hm) h t = mixedInterpolationPsi ξ s h t := by
  rw [mixedInterpolationPsi, mixedInterpolationPsi, mixedClockScheme_raiseMass,
    parisiF_raiseMass_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) p hp0 hp m hm
      (by change ξ.clock (s.q (p + 1)) = ξ.clock (s.q p); rw [hq]) le_rfl,
    mixedSchemeCorrection_eq_schemeCorrection, mixedSchemeCorrection_eq_schemeCorrection,
    schemeCorrection_raiseMass_zero_variance ξ.correction s p hp0 hp m hm hq]

theorem mixedFunctional_mergeEqualOverlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1)
    (hq : s.q (p + 1) = s.q p) (h : ℝ) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.mergeEqualOverlap p hp0 hp hq)) =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  rw [RSBScheme.mergeEqualOverlap, mixedFunctional_mergeEqualMass,
    mixedFunctional_raiseMass_zero_variance ξ s h p hp0 hp _ _ hq]

theorem mixedInterpolationPsi_mergeEqualOverlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1)
    (hq : s.q (p + 1) = s.q p) (h t : ℝ) :
    mixedInterpolationPsi ξ (s.mergeEqualOverlap p hp0 hp hq) h t = mixedInterpolationPsi ξ s h t := by
  rw [RSBScheme.mergeEqualOverlap, mixedInterpolationPsi_mergeEqualMass,
    mixedInterpolationPsi_raiseMass_zero_variance ξ s h t p hp0 hp _ _ hq]

theorem mixed_minimizer_mergeEqualOverlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1)
    (hq : s.q (p + 1) = s.q p) (h : ℝ)
    (hmin : ∀ s' : RSBScheme (k + 1), mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.mergeEqualOverlap p hp0 hp hq)) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s') := by
  intro s'
  rw [mixedFunctional_mergeEqualOverlap]
  simpa only [mixedFunctional_padZeroFirst] using hmin s'.padZeroFirst

universe u
variable {Ω : Type u} [MeasureSpace Ω]

theorem mixedGuerraPhi_mergeEqualMass {n k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1)
    (hm : s.m p = s.m (p + 1)) (h : ℝ) (U : Ω → EnergySpace n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    guerraPhi n (mixedClockScheme ξ (s.mergeEqualMass p hp hm)) (mixedBeta ξ) h U t =
      guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t := by
  rw [mixedClockScheme_mergeEqualMass]
  exact guerraPhi_mergeEqualMass (mixedClockScheme ξ s) p hp hm (mixedBeta ξ) h U ht

theorem mixedGuerraPhi_raiseMass_zero_variance {n k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Icc (s.m p) (s.m (p + 1))) (hq : s.q (p + 1) = s.q p)
    (U : Ω → EnergySpace n) (t : ℝ) :
    guerraPhi n (mixedClockScheme ξ (s.raiseMass p hp0 hp m hm)) (mixedBeta ξ) h U t =
      guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t := by
  rw [mixedClockScheme_raiseMass]
  exact guerraPhi_raiseMass_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) h p hp0 hp m hm
    (by change ξ.clock (s.q (p + 1)) = ξ.clock (s.q p); rw [hq]) U t

theorem mixedGuerraPhi_mergeEqualOverlap {n k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme (k + 1)) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1)
    (hq : s.q (p + 1) = s.q p) (h : ℝ) (U : Ω → EnergySpace n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    guerraPhi n (mixedClockScheme ξ (s.mergeEqualOverlap p hp0 hp hq)) (mixedBeta ξ) h U t =
      guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t := by
  rw [RSBScheme.mergeEqualOverlap, mixedGuerraPhi_mergeEqualMass,
    mixedGuerraPhi_raiseMass_zero_variance ξ s h p hp0 hp _ _ hq U t]
  exact ht

end FourPapersCommon
