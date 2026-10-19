module
public import FourPapersCommon.MixedGuerra

@[expose] public section

/-! Uniform endpoint control for the actual mixed interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets Set Filter
open scoped BigOperators Topology
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 600000

theorem correction_monotone_unit (ξ : AdmissibleEvenMixture) :
    MonotoneOn ξ.correction (Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn ξ.correction (Icc (0 : ℝ) 1) := by
    intro q hq
    exact (ξ.hasDerivAt_correction (by rw [abs_of_nonneg hq.1]; linarith [hq.2])).continuousAt.continuousWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
  · rw [interior_Icc]
    intro q hq
    exact (ξ.hasDerivAt_correction (by rw [abs_of_pos hq.1]; linarith [hq.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro q hq
    rw [(ξ.hasDerivAt_correction (by rw [abs_of_pos hq.1]; linarith [hq.2])).deriv]
    exact mul_nonneg hq.1.le (ξ.second_nonneg q)

theorem mixedSchemeCorrection_bounds (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) :
    0 ≤ mixedSchemeCorrection ξ s ∧ mixedSchemeCorrection ξ s ≤ ξ.correction 1 / 2 := by
  have hw (i : Fin (k + 1)) : 0 ≤ s.m (i + 1) - s.m i := sub_nonneg.mpr (s.m_mono i (by omega))
  have hq (i : Fin (k + 1)) : s.q (i + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have ht (i : Fin (k + 1)) : ξ.correction (s.q (i + 1)) ≤ ξ.correction 1 :=
    correction_monotone_unit ξ (hq i) (by norm_num) (hq i).2
  have hn (i : Fin (k + 1)) : 0 ≤ ξ.correction (s.q (i + 1)) :=
    ξ.correction_nonneg ⟨by linarith [(hq i).1], (hq i).2⟩
  have hm : (∑ i : Fin (k + 1), (s.m (i + 1) - s.m i)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => s.m (i + 1) - s.m i),
      Paper.parisiScheme_mass_telescope, s.m_top, s.m_zero]
    norm_num
  rw [mixedSchemeCorrection_eq_integral, mixedScheme_correction_integral]
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sub_nonneg.mpr (ht i))))
  · have hh : (∑ i : Fin (k + 1), (s.m (i + 1) - s.m i) *
        (ξ.correction 1 - ξ.correction (s.q (i + 1)))) ≤ ξ.correction 1 := by
      calc
        _ ≤ ∑ i : Fin (k + 1), (s.m (i + 1) - s.m i) * ξ.correction 1 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (sub_le_self _ (hn i)) (hw i))
        _ = _ := by rw [← Finset.sum_mul, hm, one_mul]
    linarith

theorem abs_tangentRemainder_bound (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : |r| ≤ 1) (hq : |q| ≤ 1) :
    |ξ.tangentRemainder r q| ≤ 2 * (ξ.value 1 + ξ.variance) := by
  have hs : |r - q| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hm := mul_le_mul (ξ.abs_first_le_variance hq) hs (abs_nonneg _) ξ.variance_pos.le
  unfold AdmissibleEvenMixture.tangentRemainder
  calc
    _ ≤ |ξ.value r - ξ.value q| + |ξ.first q * (r - q)| := abs_sub _ _
    _ ≤ (ξ.value 1 + ξ.value 1) + ξ.variance * 2 := add_le_add
      ((abs_sub _ _).trans (add_le_add (ξ.abs_value_le_at_one hr) (ξ.abs_value_le_at_one hq)))
      (by simpa only [abs_mul] using hm)
    _ = _ := by ring

theorem mixedGuerraRemainder_le {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace N) (t : ℝ) :
    mixedGuerraRemainder ξ s h U t ≤ ξ.value 1 + ξ.variance := by
  unfold mixedGuerraRemainder
  split_ifs with ht
  · have hb (ω : Ω) :
        ‖guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (U ω) h t
          (fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l))) (k + 2) 0‖ ≤
          2 * (ξ.value 1 + ξ.variance) := by
      have hh := guerraReplicaAccum_abs_le N (mixedClockScheme ξ s) (mixedBeta ξ) (U ω) h ht
        (K := fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l)))
        (C := 2 * (ξ.value 1 + ξ.variance))
        (mul_nonneg (by norm_num) (add_nonneg ξ.value_one_nonneg ξ.variance_pos.le))
        (fun l σ τ => abs_tangentRemainder_bound ξ (abs_overlap_le_one hN σ τ) (by
          rw [abs_of_nonneg (s.q_nonneg (by omega))]; exact s.q_le_one (by omega))) (k + 2) 0
      simpa only [guerraMass_top, sub_zero, mul_one, Real.norm_eq_abs] using hh
    have hh := norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall hb)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at hh
    have hl := (le_abs_self (∫ ω,
      guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (U ω) h t
        (fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l))) (k + 2) 0 ∂ℙ)).trans hh
    linarith
  · exact add_nonneg ξ.value_one_nonneg ξ.variance_pos.le

def mixedGuerraDerivativeBound (ξ : AdmissibleEvenMixture) : ℝ :=
  2 * (ξ.value 1 + ξ.variance)

theorem mixedGuerraDerivativeBound_pos (ξ : AdmissibleEvenMixture) : 0 < mixedGuerraDerivativeBound ξ :=
  mul_pos (by norm_num) (add_pos_of_nonneg_of_pos ξ.value_one_nonneg ξ.variance_pos)

theorem mixedGuerraPhi_endpoint_lower {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t -
      mixedGuerraDerivativeBound ξ * (1 - t) ≤
        free_entropy (Ω := Ω) (N := N) (β := mixedBeta ξ) (h := h) sk.U := by
  obtain ⟨hc, _, hd⟩ := mixed_guerra_identity hN ξ sk s h
  have hdiff : DifferentiableOn ℝ (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U)
      (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hge : ∀ x ∈ interior (Icc (0 : ℝ) 1),
      -mixedGuerraDerivativeBound ξ ≤ deriv (guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U) x := by
    rw [interior_Icc]
    intro x hx
    rw [(hd x hx).deriv]
    have hh := (mixedSchemeCorrection_bounds ξ s).2
    have hr := mixedGuerraRemainder_le hN ξ s h sk.U x
    rw [ξ.correction_one] at hh
    unfold mixedGuerraDerivativeBound
    linarith [ξ.value_one_nonneg, ξ.variance_pos]
  have hh := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hc hdiff hge
    t ht 1 (by simp) ht.2
  rw [guerraPhi_one N hN] at hh
  linarith

end FourPapersCommon
