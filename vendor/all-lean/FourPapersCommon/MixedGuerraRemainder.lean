module
public import FourPapersCommon.MixedGuerraDisorder
public import FourPapersCommon.MixedScheme

@[expose] public section

/-! The genuine nonnegative convex-covariance remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets Set Filter
open PhysLean.Probability.GaussianIBP
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixedGuerraReplicaAccum_tangent {N : ℕ} (hN : 0 < N)
    (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    (U : EnergySpace N) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) U h t
      (fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l))) j y =
      guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) U h t
        (fun _ σ τ => ξ.value (overlap N σ τ)) j y -
      ξ.variance * guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) U h t
        (fun l σ τ => (mixedClockScheme ξ s).q (k + 2 - l) * overlap N σ τ) j y +
      ∑ l ∈ Finset.range j,
        (guerraMass (mixedClockScheme ξ s) l - guerraMass (mixedClockScheme ξ s) (l + 1)) *
          ξ.correction (s.q (k + 2 - l)) := by
  let c : Fin 3 → ℝ := ![1, -1, 1]
  let K : Fin 3 → ℕ → Config N → Config N → ℝ :=
    ![fun _ σ τ => ξ.value (overlap N σ τ),
      fun l σ τ => ξ.first (s.q (k + 2 - l)) * overlap N σ τ,
      fun l _ _ => ξ.correction (s.q (k + 2 - l))]
  have hq (l : ℕ) : |s.q (k + 2 - l)| ≤ 1 := by
    rw [abs_of_nonneg (s.q_nonneg (by omega))]
    exact s.q_le_one (by omega)
  have hK : ∀ i l σ τ, |K i l σ τ| ≤ ξ.variance + ξ.value 1 := by
    intro i l σ τ
    fin_cases i
    · exact (ξ.abs_value_le_at_one (abs_overlap_le_one hN σ τ)).trans
        (le_add_of_nonneg_left ξ.variance_pos.le)
    · change |ξ.first (s.q (k + 2 - l)) * overlap N σ τ| ≤ _
      rw [abs_mul]
      exact (mul_le_mul (ξ.abs_first_le_variance (hq l)) (abs_overlap_le_one hN σ τ)
        (abs_nonneg _) ξ.variance_pos.le).trans (by simp; exact ξ.value_one_nonneg)
    · exact ξ.abs_correction_le (hq l)
  have he : (fun l σ τ => ∑ i, c i * K i l σ τ) =
      fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l)) := by
    funext l σ τ
    simp [c, K, Fin.sum_univ_succ, ξ.tangentRemainder_eq]
    ring
  have hh := guerraReplicaAccum_sum_mul N (mixedClockScheme ξ s) (mixedBeta ξ) U h ht
    c K (fun _ => ξ.variance + ξ.value 1) hK j y
  rw [he] at hh
  have hfirst : (fun l σ τ => ξ.first (s.q (k + 2 - l)) * overlap N σ τ) =
      fun l σ τ => ξ.variance * ((mixedClockScheme ξ s).q (k + 2 - l) * overlap N σ τ) := by
    funext l σ τ
    simp only [mixedClockScheme_q, AdmissibleEvenMixture.clock]
    field_simp [ξ.variance_pos.ne']
  simpa [c, K, Fin.sum_univ_succ, hfirst, guerraReplicaAccum_const_level N
    (mixedClockScheme ξ s) (mixedBeta ξ) U h ht,
    guerraReplicaAccum_const_mul N (mixedClockScheme ξ s) (mixedBeta ξ) U h t,
    sub_eq_add_neg, add_assoc] using hh

def mixedGuerraRemainder {N : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace N) (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then (1 / 2) * ∫ ω,
    guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (U ω) h t
      (fun l σ τ => ξ.tangentRemainder (overlap N σ τ) (s.q (k + 2 - l))) (k + 2) 0 ∂ℙ
  else 0

theorem mixedGuerraRemainder_nonneg {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace N) (t : ℝ) :
    0 ≤ mixedGuerraRemainder ξ s h U t := by
  unfold mixedGuerraRemainder
  split_ifs with ht
  · apply mul_nonneg (by norm_num)
    apply integral_nonneg
    intro ω
    apply guerraReplicaAccum_nonneg N (mixedClockScheme ξ s) (mixedBeta ξ) (U ω) h ht
    intro l σ τ
    exact ξ.tangentRemainder_nonneg (abs_le.mp (abs_overlap_le_one hN σ τ))
      ⟨by linarith [s.q_nonneg (p := k + 2 - l) (by omega)], s.q_le_one (by omega)⟩
  · exact le_rfl

theorem mixedGuerraRemainder_expansion {N : ℕ} (hN : 0 < N) (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    mixedGuerraRemainder ξ s h sk.U t = (1 / 2) *
      ((∫ ω, guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (sk.U ω) h t
          (fun _ σ τ => ξ.value (overlap N σ τ)) (k + 2) 0 ∂ℙ) -
        ξ.variance * (∫ ω, guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (sk.U ω) h t
          (fun l σ τ => (mixedClockScheme ξ s).q (k + 2 - l) * overlap N σ τ) (k + 2) 0 ∂ℙ) +
        ∑ l ∈ Finset.range (k + 2),
          (guerraMass (mixedClockScheme ξ s) l - guerraMass (mixedClockScheme ξ s) (l + 1)) *
            ξ.correction (s.q (k + 2 - l))) := by
  have hR := mixed_integrable_guerraReplicaAccum (mixedBeta ξ) h sk.U sk.hU (mixedClockScheme ξ s) ht
    (fun _ σ τ => ξ.abs_value_le_at_one (abs_overlap_le_one hN σ τ)) (k + 2) 0
  have hQ := mixed_integrable_guerraReplicaAccum (mixedBeta ξ) h sk.U sk.hU (mixedClockScheme ξ s) ht
    (abs_q_mul_overlap_le_one hN (mixedClockScheme ξ s)) (k + 2) 0
  unfold mixedGuerraRemainder
  rw [ite_eq_left ht]
  simp_rw [mixedGuerraReplicaAccum_tangent hN ξ s h _ ht]
  change (1 / 2) * ∫ ω, ((fun ω =>
    guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (sk.U ω) h t
      (fun _ σ τ => ξ.value (overlap N σ τ)) (k + 2) 0) -
    (fun ω => ξ.variance * guerraReplicaAccum N (mixedClockScheme ξ s) (mixedBeta ξ) (sk.U ω) h t
      (fun l σ τ => (mixedClockScheme ξ s).q (k + 2 - l) * overlap N σ τ) (k + 2) 0)) ω + _ = _
  rw [integral_add (hR.sub (hQ.const_mul ξ.variance)) (integrable_const _)]
  simp only [Pi.sub_apply]
  rw [integral_sub hR (hQ.const_mul ξ.variance), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

end FourPapersCommon
