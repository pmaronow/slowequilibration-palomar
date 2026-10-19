module
public import FourPapersCommon.MixedGuerraSource
public import FourPapersCommon.MixedGuerraRemainder

@[expose] public section

/-! Genuine Guerra identity and upper bound for all admissible even mixtures. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets Set Filter
open scoped BigOperators Topology
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixed_guerra_identity {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ) :
    ContinuousOn (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U) (Icc (0 : ℝ) 1) ∧
      (∀ t, 0 ≤ mixedGuerraRemainder ξ s h sk.U t) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U)
          (-mixedSchemeCorrection ξ s - mixedGuerraRemainder ξ s h sk.U t) t := by
  refine ⟨mixed_continuousOn_guerraPhi (mixedBeta ξ) h sk.U sk.hU (mixedClockScheme ξ s),
    mixedGuerraRemainder_nonneg hN ξ s h sk.U, ?_⟩
  intro t ht
  refine (mixed_hasDerivAt_guerraPhi (mixedBeta ξ) h sk.U sk.hU (mixedClockScheme ξ s) ht).congr_deriv ?_
  rw [mixedGuerraD_top_expectation hN (mixedBeta ξ) h ξ sk (mixedClockScheme ξ s) ht,
    mixedGuerraRemainder_expansion hN ξ sk s h ht, mixedSchemeCorrection, ξ.correction_one,
    mixedBeta_sq]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNR]
  ring

theorem mixed_guerra_rsb_bound {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ) :
    free_entropy (Ω := Ω) (N := N) (β := mixedBeta ξ) (h := h) sk.U ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  obtain ⟨hcont, hRem, hderiv⟩ := mixed_guerra_identity hN ξ sk s h
  have hdiff : DifferentiableOn ℝ (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U)
      (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hle : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      deriv (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U) t ≤
        -mixedSchemeCorrection ξ s := by
    rw [interior_Icc]
    intro t ht
    rw [(hderiv t ht).deriv]
    linarith [hRem t]
  have hmvt := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff hle
    0 (by simp) 1 (by simp) zero_le_one
  rw [guerraPhi_one N hN, guerraPhi_zero N hN] at hmvt
  rw [mixedFunctional_scheme ξ s h]
  simp only [sub_zero, mul_one] at hmvt
  linarith

end FourPapersCommon
