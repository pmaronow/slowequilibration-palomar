module
public import FourPapersCommon.MixedInsertedFunctional
public import FourPapersCommon.SchemeCorrectionAlgebra
public import Targets.Section4EndpointOptimality

@[expose] public section

/-! Genuine noninitial endpoint optimality for the physical mixed functional. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem schemeCorrection_raiseMass_zero_variance (θ : ℝ → ℝ) {k : ℕ}
    (s : RSBScheme k) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Icc (s.m p) (s.m (p + 1))) (hq : s.q (p + 1) = s.q p) :
    schemeCorrection θ (s.raiseMass p hp0 hp m hm) = schemeCorrection θ s := by
  unfold schemeCorrection
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (if j = p then m else s.m j) * (θ (s.q (j + 1)) - θ (s.q j)) = _
  by_cases he : j = p
  · subst j
    simp [hq]
  · rw [ite_eq_right he]

theorem mixedClockScheme_raiseMass (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Icc (s.m p) (s.m (p + 1))) :
    mixedClockScheme ξ (s.raiseMass p hp0 hp m hm) =
      (mixedClockScheme ξ s).raiseMass p hp0 hp m hm := by
  rfl

theorem mixedFunctional_raiseMass_zero_variance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Icc (s.m p) (s.m (p + 1))) (hq : s.q (p + 1) = s.q p) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.raiseMass p hp0 hp m hm)) =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  rw [mixedFunctional_scheme, mixedFunctional_scheme, mixedClockScheme_raiseMass,
    parisiF_raiseMass_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) p hp0 hp m hm
      (by change ξ.clock (s.q (p + 1)) = ξ.clock (s.q p); rw [hq]) le_rfl]
  congr 1
  rw [mixedSchemeCorrection_eq_schemeCorrection, mixedSchemeCorrection_eq_schemeCorrection,
    schemeCorrection_raiseMass_zero_variance ξ.correction s p hp0 hp m hm hq]

theorem mixedSection4Phi_lower_overlap_min {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    mixedSection4Phi ξ s h r (s.m (r - 1)) (s.q (r - 1)) ≤
      mixedSection4Phi ξ s h r m (s.q (r - 1)) := by
  have hu : s.q (r - 1) ∈ Set.Icc (s.q (r - 1)) (s.q r) :=
    ⟨le_rfl, s.q_mono' r (by omega) (r - 1) (by omega)⟩
  let si := s.insertLevel r (by omega) hr m (s.q (r - 1)) hm hu
  have hm' : m ∈ Set.Icc (si.m (r - 1)) (si.m (r - 1 + 1)) := by
    simpa [si, RSBScheme.insertLevel, section4Mass, show r - 1 < r by omega,
      show r - 1 + 1 = r by omega] using (⟨hm.1, le_rfl⟩ : m ∈ Set.Icc (s.m (r - 1)) m)
  let sj := si.raiseMass (r - 1) (by omega) (by omega) m hm'
  have hq : si.q (r - 1 + 1) = si.q (r - 1) := by
    simp [si, RSBScheme.insertLevel, section5Rho, show r - 1 + 1 = r by omega,
      show r - 1 < r by omega]
  have he : sj.m (r - 1) = sj.m (r - 1 + 1) := by
    simp [sj, RSBScheme.raiseMass, si, RSBScheme.insertLevel, section4Mass,
      show r - 1 + 1 = r by omega]
  have H := hmin (sj.mergeEqualMass (r - 1) (by omega) he)
  rw [mixedFunctional_mergeEqualMass] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure
    (si.raiseMass (r - 1) (by omega) (by omega) m hm')) at H
  rw [mixedFunctional_raiseMass_zero_variance ξ si h (r - 1) (by omega) (by omega) m hm' hq] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure
    (s.insertLevel r (by omega) hr m (s.q (r - 1)) hm hu)) at H
  rwa [mixedFunctional_insertLevel, ← mixedSection4Phi_baseline ξ s h (by omega) hr hu] at H

/-- The lower-endpoint part of Proposition 4.8 for noninitial intervals.
Strictness of the adjacent mass gap provides actual admissible right variations;
near-global minimality is not substituted for fixed-level minimality. -/
theorem mixedSection4FirstVariation_lower_nonneg {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    0 ≤ mixedSection4FirstVariation ξ s h r (s.q (r - 1)) := by
  have hu : s.q (r - 1) ∈ Set.Icc (s.q (r - 1)) (s.q r) :=
    ⟨le_rfl, s.q_mono' r (by omega) (r - 1) (by omega)⟩
  have H := (hasDerivAt_mixedSection4Phi_mass_baseline ξ s h (by omega) hr hu).tendsto_slope_zero_right
  apply ge_of_tendsto H
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hm)] with t ht
  have hm' : s.m (r - 1) + t ∈ Set.Icc (s.m (r - 1)) (s.m r) := by
    constructor <;> linarith [ht.1, ht.2]
  have hcomp := mixedSection4Phi_lower_overlap_min ξ s h hr0 hr hm' hmin
  exact smul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr hcomp)

end FourPapersCommon
