module
public import FourPapersCommon.MixedInsertedFunctional
public import Targets.Section4QuantitativeOptimality

@[expose] public section

/-! Uniform quantitative optimality of genuine mixed scheme insertions.

The second mass derivative belongs to the actual clocked Gaussian recursion;
θ contributes a linear mass term. Competitors and the minimum are the actual
mixed functional, never the SK functional at the normalized clock.
-/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedSection4Phi_mass_taylor_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {m u : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4Phi ξ s h r m u - mixedFunctional ξ h (Paper.parisiSchemeMeasure s) -
      mixedSection4FirstVariation ξ s h r u * (m - s.m (r - 1))| ≤
        section4MassSecondBound ((mixedBeta ξ) ^ 2) * (m - s.m (r - 1)) ^ 2 := by
  have ha : s.m (r - 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hv := mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  have HT := section4T_mass_taylor_bound (mixedClockScheme ξ s) (mixedBeta ξ) h hr ha hm hv
  have hD := (hasDerivAt_section4T_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv).deriv
  have hbase := section4T_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv
  simp only [mixedClockScheme_m] at hD hbase
  rw [hD, hbase] at HT
  rw [mixedSection4Phi, mixedFunctional_scheme, mixedSection4FirstVariation]
  convert! HT using 1
  congr 1
  ring

theorem mixedSection4FirstVariation_lower_bound (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    -section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε ≤ mixedSection4FirstVariation ξ s h r u := by
  let C := section4MassSecondBound ((mixedBeta ξ) ^ 2) + 1
  have hC : 0 < C := by dsimp [C]; linarith [section4MassSecondBound_nonneg ((mixedBeta ξ) ^ 2)]
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  by_cases hf : 0 ≤ mixedSection4FirstVariation ξ s h r u
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (section4OptimalityBound_pos (mixedBeta ξ)).le) (Real.sqrt_nonneg ε)) hf
  have hTaylor (m : ℝ) (hm : m ∈ Icc (s.m (r - 1)) (s.m r)) :
      mixedSection4Phi ξ s h r m u - mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedSection4FirstVariation ξ s h r u * (m - s.m (r - 1)) + C * (m - s.m (r - 1)) ^ 2 := by
    have H := (abs_le.mp (mixedSection4Phi_mass_taylor_baseline ξ s h hr0 hr
      ⟨(s.m_nonneg (by omega)).trans hm.1, hm.2.trans (s.m_le_one hr)⟩ hu)).2
    dsimp [C]
    nlinarith [sq_nonneg (m - s.m (r - 1))]
  have hupper : 0 ≤ mixedSection4FirstVariation ξ s h r u * (s.m r - s.m (r - 1)) +
      C * (s.m r - s.m (r - 1)) ^ 2 := by
    have H := mixedSection4Phi_upper_mass_min ξ s h hr0 hr hu hmin
    rw [mixedSection4Phi_baseline ξ s h hr0 hr hu] at H
    linarith [hTaylor (s.m r) ⟨hgap.le, le_rfl⟩]
  have hcomp (δ : ℝ) (hδ : δ ∈ Icc (0 : ℝ) (s.m r - s.m (r - 1))) :
      -ε ≤ mixedSection4FirstVariation ξ s h r u * δ + C * δ ^ 2 := by
    have hm : s.m (r - 1) + δ ∈ Icc (s.m (r - 1)) (s.m r) := by
      constructor <;> linarith [hδ.1, hδ.2]
    have H := mixedSection4Phi_near_min ξ s h ε hr0 hr hm hu hnear
    rw [mixedSection4Phi_baseline ξ s h hr0 hr hu] at H
    have HT := hTaylor (s.m (r - 1) + δ) hm
    simp only [add_sub_cancel_left] at HT
    linarith
  have hsq := firstVariation_sq_le_of_quadratic_comparisons hC hgap (lt_of_not_ge hf) hupper hcomp
  have H : -mixedSection4FirstVariation ξ s h r u ≤ Real.sqrt (4 * C * ε) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [neg_sq] using hsq
  have hsqrt : Real.sqrt (4 * C * ε) = section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε := by
    rw [Real.sqrt_mul' (4 * C) hε, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [section4OptimalityBound, C]
  rw [hsqrt] at H
  linarith

end FourPapersCommon
