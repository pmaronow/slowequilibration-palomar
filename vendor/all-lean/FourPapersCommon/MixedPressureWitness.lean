module
public import FourPapersCommon.MixedLeftCompact
public import FourPapersCommon.MixedRightCompact
public import FourPapersCommon.MixedInterleavedCompactGaps

@[expose] public section

/-! A common continuous scalar witness family for physical mixed pressure.
Trial overlaps are fixed inside each witness, while the actual constrained
overlap varies continuously in the scalar majorant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

inductive MixedPressureWitness {k : ℕ} (s : RSBScheme k) (r : ℕ)
  | left (m v ell : ℝ) (hm : m ∈ Icc (s.m (r - 1) / 2) (s.m r))
      (hv : v ∈ Icc (s.q (r - 1)) (s.q r))
  | right (m v ell : ℝ) (hm : m ∈ Icc (s.m (r - 1)) (2 * s.m r))
      (hv : v ∈ Icc (s.q r) (s.q (r + 1)))
  | interleavedBase (j : ℕ) (v ell : ℝ) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
      (hv : |v| ∈ Icc (s.q (j - 1)) (s.q j))
  | interleaved (j : ℕ) (v ell : ℝ) (hj0 : 1 ≤ j) (hj : j ≤ k + 2)
      (hv : |v| ∈ Icc (s.q (j - 1)) (s.q j))

def mixedPressureWitnessDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (w : MixedPressureWitness s r) (p : ℝ × ℝ) : ℝ :=
  match w with
  | .left m v ell _ _ =>
      2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
        section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r m
          (mixedLeftSplitVariance ξ s r p.1 v) ell + ell * p.2 +
        p.1 * (m - s.m (r - 1)) * (ξ.correction (s.q r) - ξ.correction v) -
        p.1 * ξ.tangentRemainder p.2 v
  | .right m v ell _ _ =>
      2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
        section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r m
          (mixedRightSplitVariance ξ s r p.1 v) ell + ell * p.2 +
        p.1 * (m - s.m r) * (ξ.correction v - ξ.correction (s.q r)) -
        p.1 * ξ.tangentRemainder p.2 v
  | .interleavedBase j v ell _ _ _ =>
      mixedInterleavedComparisonDeficit ξ s h r j v ell p
  | .interleaved j v ell _ _ _ =>
      mixedInterleavedComparisonDeficit ξ s.padOneLast h r j v ell p

theorem mixedPressureWitnessDeficit_left_at_trial (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (m v ell t : ℝ)
    (hm : m ∈ Icc (s.m (r - 1) / 2) (s.m r)) (hv : v ∈ Icc (s.q (r - 1)) (s.q r)) :
    mixedPressureWitnessDeficit ξ s h r (.left m v ell hm hv) (t, v) =
      mixedLeftComparisonDeficit ξ s h r m ell (t, v) := by
  simp only [mixedPressureWitnessDeficit, mixedLeftComparisonDeficit, mixedLeftComparison,
    mixedInterpolationPsi, tangentRemainder_self, mul_zero, sub_zero]
  ring

theorem mixedPressureWitnessDeficit_right_at_trial (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (m v ell t : ℝ)
    (hm : m ∈ Icc (s.m (r - 1)) (2 * s.m r)) (hv : v ∈ Icc (s.q r) (s.q (r + 1))) :
    mixedPressureWitnessDeficit ξ s h r (.right m v ell hm hv) (t, v) =
      mixedRightComparisonDeficit ξ s h r m ell (t, v) := by
  simp only [mixedPressureWitnessDeficit, mixedRightComparisonDeficit, mixedRightComparison,
    mixedInterpolationPsi, tangentRemainder_self, mul_zero, sub_zero]
  ring

theorem continuousOn_mixedPressureWitnessDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) (w : MixedPressureWitness s r)
    {S : Set (ℝ × ℝ)} (hunit : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    ContinuousOn (mixedPressureWitnessDeficit ξ s h r w) S := by
  have hR (v : ℝ) : ContinuousOn (fun p : ℝ × ℝ => ξ.tangentRemainder p.2 v) S := by
    unfold AdmissibleEvenMixture.tangentRemainder
    exact ((ξ.continuousOn_value.comp continuous_snd.continuousOn hunit).sub continuousOn_const).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub continuousOn_const))
  cases w with
  | left m v ell hm hv =>
      have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
      have H := (continuous_section5V_variance_lambda (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm0).comp
        (show Continuous (fun p : ℝ × ℝ => (mixedLeftSplitVariance ξ s r p.1 v, ell)) by
          unfold mixedLeftSplitVariance
          fun_prop)
      exact (((continuousOn_const.sub H.continuousOn).add
        (continuousOn_const.mul continuous_snd.continuousOn)).add
        ((continuous_fst.continuousOn.mul continuousOn_const).mul continuousOn_const)).sub
        (continuous_fst.continuousOn.mul (hR v))
  | right m v ell hm hv =>
      have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
      have H := (continuous_section5RightV_variance_lambda (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm0).comp
        (show Continuous (fun p : ℝ × ℝ => (mixedRightSplitVariance ξ s r p.1 v, ell)) by
          unfold mixedRightSplitVariance
          fun_prop)
      exact (((continuousOn_const.sub H.continuousOn).add
        (continuousOn_const.mul continuous_snd.continuousOn)).add
        ((continuous_fst.continuousOn.mul continuousOn_const).mul continuousOn_const)).sub
        (continuous_fst.continuousOn.mul (hR v))
  | interleavedBase j v ell hj0 hj hv =>
      exact continuousOn_mixedInterleavedComparisonDeficit ξ s h r hj hv ell hunit
  | interleaved j v ell hj0 hj hv =>
      exact continuousOn_mixedInterleavedComparisonDeficit ξ s.padOneLast h r (by omega)
        (by simpa only [s.padOneLast_q (p := j - 1) (by omega), s.padOneLast_q hj] using hv) ell hunit

universe u
theorem mixed_constrainedPhi_le_pressureWitness
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (w : MixedPressureWitness s r) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t - mixedPressureWitnessDeficit ξ s h r w (t, u) := by
  letI : Nonempty (AT.ConstrainedPair n u) := by
    obtain ⟨σ, τ, hστ⟩ := hatt
    exact ⟨⟨(σ, τ), hστ⟩⟩
  cases w with
  | left m v ell hm hv =>
      have H := mixedLeft_constrainedPhi_le hn ξ s h sk (u := u) (v := v) hr0 hr hm ht hv ell
      dsimp [mixedPressureWitnessDeficit, mixedInterpolationPsi]
      linarith only [H]
  | right m v ell hm hv =>
      have H := mixedRight_constrainedPhi_le hn ξ s h sk (u := u) (v := v) hr0 hr hm ht hv ell
      dsimp [mixedPressureWitnessDeficit, mixedInterpolationPsi]
      linarith only [H]
  | interleavedBase j v ell hj0 hj hv =>
      exact mixed_constrainedPhi_le_interleavedComparison hn ξ s h sk hr0 hr hj0 hj
        (ell := ell) ht hv hatt
  | interleaved j v ell hj0 hj hv =>
      have H := mixed_constrainedPhi_le_interleavedComparison hn ξ s.padOneLast h sk
        hr0 (by omega) hj0 (by omega) (ell := ell) ht
        (by simpa only [s.padOneLast_q (p := j - 1) (by omega), s.padOneLast_q hj] using hv) hatt
      simpa only [mixedPressureWitnessDeficit, mixedClockScheme_padOneLast,
        show k + 1 + 2 - r = (k + 2 - r) + 1 by omega,
        constrainedPhi_padOneLast, mixedInterpolationPsi_padOneLast] using H

theorem exists_mixed_constrainedPhi_compact_pressureWitness_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (hunit : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1)
    (ht : ∀ p ∈ S, p.1 ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ p ∈ S, ∃ w : MixedPressureWitness s r,
      0 < mixedPressureWitnessDeficit ξ s h r w p) :
    ∃ δ > (0 : ℝ), ∀ (Ω : Type u) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀ p ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      (∃ σ τ : Config n, overlap n σ τ = p.2) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) p.1 p.2 ≤
        2 * mixedInterpolationPsi ξ s h p.1 - δ := by
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS
    (mixedPressureWitnessDeficit ξ s h r)
    (fun w => continuousOn_mixedPressureWitnessDeficit ξ s h hr w hunit) hpos
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ _ p hp n hn sk hatt
  obtain ⟨w, hw⟩ := Hδ p hp
  exact (mixed_constrainedPhi_le_pressureWitness hn ξ s h sk hr0 hr w (ht p hp) hatt).trans
    (by linarith only [hw])

end FourPapersCommon
