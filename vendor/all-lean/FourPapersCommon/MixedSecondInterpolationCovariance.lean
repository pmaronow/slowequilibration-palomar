module
public import FourPapersCommon.MixedGuerraDisorder
public import Targets.CoupledReplicaTrace

@[expose] public section

/-! The actual four-overlap mixed covariance in the second Gaussian
interpolation. The tangent remainder is evaluated at physical overlaps;
the field covariance uses their first covariance derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
set_option maxHeartbeats 800000

def mixedPairCovariance {n : ℕ} (ξ : AdmissibleEvenMixture)
    (p q : Config n × Config n) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, ξ.value (AT.pairOverlapMatrix p q a b)

def mixedPairCovarianceDefect {n : ℕ} (ξ : AdmissibleEvenMixture) (q c : ℝ)
    (p z : Config n × Config n) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    ξ.tangentRemainder (AT.pairOverlapMatrix p z a b) (pairTrialMatrix q c a b)

theorem mixedPairCovariance_self {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) {u : ℝ} (p : AT.ConstrainedPair n u) :
    mixedPairCovariance ξ p.1 p.1 = 2 * (ξ.value 1 + ξ.value u) := by
  simp [mixedPairCovariance, AT.pairOverlapMatrix_self hn, Fin.sum_univ_two]
  ring

theorem mixedPairCovariance_completion {n : ℕ} (ξ : AdmissibleEvenMixture)
    (q c : ℝ) (p z : Config n × Config n) :
    mixedPairCovariance ξ p z - pairFieldCovariance 1 (ξ.first q) (ξ.first c) p z =
      mixedPairCovarianceDefect ξ q c p z - 2 * (ξ.correction q + ξ.correction c) := by
  norm_num [mixedPairCovariance, mixedPairCovarianceDefect, pairFieldCovariance,
    Fin.sum_univ_two, pairTrialMatrix, AdmissibleEvenMixture.tangentRemainder_eq]
  ring

theorem mixedPairCovarianceDefect_nonneg {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) {q c : ℝ}
    (hq : q ∈ Icc (-1 : ℝ) 1) (hc : c ∈ Icc (-1 : ℝ) 1)
    (p z : Config n × Config n) : 0 ≤ mixedPairCovarianceDefect ξ q c p z := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply ξ.tangentRemainder_nonneg
  · exact abs_le.mp (abs_overlap_le_one hn (AT.pairConfig p a) (AT.pairConfig z b))
  · fin_cases a <;> fin_cases b <;> simpa [pairTrialMatrix] using (by assumption : _)

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixedPairCovariance_spectral_sum {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) (p q : Config n × Config n) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      (sk.hU.w i p.1 + sk.hU.w i p.2) * (sk.hU.w i q.1 + sk.hU.w i q.2)) =
      n * mixedPairCovariance ξ p q := by
  have he (i : sk.hU.ι) : (sk.hU.τ i : ℝ) *
      (sk.hU.w i p.1 + sk.hU.w i p.2) * (sk.hU.w i q.1 + sk.hU.w i q.2) =
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.1 * sk.hU.w i q.1) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.1 * sk.hU.w i q.2) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.2 * sk.hU.w i q.1) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.2 * sk.hU.w i q.2) := by ring
  simp_rw [he, Finset.sum_add_distrib, mixedDisorder_covariance_spectral_sum ξ sk]
  simp [mixedPairCovariance, AT.pairOverlapMatrix, AT.pairConfig, Fin.sum_univ_two]
  ring

theorem constrainedPairFieldCascadeSecond_mixed_trace {n : ℕ}
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d j U (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (2 * (ξ.value 1 + ξ.value u) -
        constrainedReplicaMoment m v d 0 j U u (fun p q => mixedPairCovariance ξ p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          constrainedReplicaMoment m v d l (j - l) U u (fun p q => mixedPairCovariance ξ p.1 q.1) x y -
          constrainedReplicaMoment m v d (l + 1) (j - (l + 1)) U u
            (fun p q => mixedPairCovariance ξ p.1 q.1) x y)) := by
  simp only [constrainedPairFieldCascadeSecond_eq_replica U _ _ u m v hm hv d j x y,
    constrainedReplicaHessianExpression]
  rw [sum_weighted_covariance, sum_weighted_diagonal, constrainedReplicaBilinear_contraction]
  simp_rw [constrainedReplicaBilinear_contraction, mixedPairCovariance_spectral_sum ξ sk,
    mixedPairCovariance_self hn ξ, constrainedReplicaMoment_const_mul]
  rw [← Finset.sum_mul, sum_constrainedCascadeGibbs U u m v hm hv d j x y, one_mul]
  simp_rw [← mul_sub (n : ℝ), mul_left_comm (m _) (n : ℝ)]
  rw [← Finset.mul_sum]
  ring

theorem integral_constrainedPairFieldCascadeSecond_mixed_trace {n : ℕ}
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d j (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (2 * (ξ.value 1 + ξ.value u) -
        averagedConstrainedReplicaMoment Z m v d 0 j u (fun p q => mixedPairCovariance ξ p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          averagedConstrainedReplicaMoment Z m v d l (j - l) u
            (fun p q => mixedPairCovariance ξ p.1 q.1) x y -
          averagedConstrainedReplicaMoment Z m v d (l + 1) (j - (l + 1)) u
            (fun p q => mixedPairCovariance ξ p.1 q.1) x y)) := by
  let K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ :=
    fun p q => mixedPairCovariance ξ p.1 q.1
  have hi (l r : ℕ) := integrable_constrainedReplicaMoment hZ u m v hm hv d l r K x y
  have hs : Integrable (fun ω => ∑ l : Fin j, m l * (
      constrainedReplicaMoment m v d l (j - l) (Z ω) u K x y -
      constrainedReplicaMoment m v d (l + 1) (j - (l + 1)) (Z ω) u K x y)) :=
    integrable_finsetSum _ (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp_rw [constrainedPairFieldCascadeSecond_mixed_trace hn ξ sk _ u m v hm hv d j x y]
  have hlin := integral_add ((integrable_const (2 * (ξ.value 1 + ξ.value u))).sub (hi 0 j)) hs
  simp only [Pi.sub_apply, K] at hlin
  rw [integral_const_mul, hlin,
    integral_sub (integrable_const (2 * (ξ.value 1 + ξ.value u))) (hi 0 j), integral_const,
    probReal_univ, smul_eq_mul, one_mul,
    integral_constrainedReplicaMoment hZ u m v hm hv d 0 j _ x y]
  congr 2
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin j)) (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp only [Pi.sub_apply, K] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_sub (hi l (j - l)) (hi (l + 1) (j - (l + 1))),
    integral_constrainedReplicaMoment hZ u m v hm hv,
    integral_constrainedReplicaMoment hZ u m v hm hv]

end FourPapersCommon
