-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairResidualScoreCoercivity
public import SlowEquilibration.GaussianGramLogPerturbation
public import SlowEquilibration.GaussianIndependentPairDensity

/-! Actual conditional pair-score density factorization, with constants
chosen before dimension and every conditioning score target. -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity PairObservationNormBounds NormalizedObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The genuine residual score law after both tangent-gradient observations
has a pointwise density-ratio error K(1+‖w‖²)|overlap|^d against the independent
one-point score reference. Neither the inverse nor the density error is assumed. -/
theorem uniform_residual_pair_score_density (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=residualPairScore c x y e f
      Surjective A ∧ ∀ w : ScorePairSpace,
        |Real.log (realObservationDensity A w/realObservationDensity (referenceScorePair μ Q) w)| ≤
          K*(1+‖w‖^2)*|overlap x y|^μ.minDegree := by
  obtain ⟨r,δ,hr,hδ,hall⟩:=uniform_residual_pair_score_coercivity μ hQ hnp hdeg
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  have hL : 0 < L := profileBound_pos c
  let B:=referenceScorePair μ Q
  have hRef : Surjective (referenceScore μ Q) :=
    center_score_surjective (by norm_num) μ hQ hnp referencePoint (by simpa using NormalizedObservationCoercivity.referencePoint_norm_sq)
  have hB : Surjective B := independentPair_surjective _ _ hRef hRef
  let M:=‖((squareObservation B hB).symm : ScorePairSpace →L[ℝ] ScorePairSpace)‖^2
  let T:=‖(gram B).inverse‖
  let J:=10*L+36*L^2/δ
  have hM : 0 ≤ M := sq_nonneg _
  have hT : 0 ≤ T := norm_nonneg _
  have hJ : 0 < J := by dsimp [J];positivity
  let D:=4*M*J
  let C:=J*T/(2*δ)
  let K:=D+C+1
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hK : 0 < K := by dsimp [K];positivity
  let ρ0:=min r (min 1 (1/(2*(M+1)*J)))
  have hρ0 : 0 < ρ0 := lt_min hr (lt_min (by norm_num) (by positivity))
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ
  have hρr : |overlap x y| ≤ r := hρ.trans (min_le_left _ _)
  have hρ1 : |overlap x y| ≤ 1 :=
    (hρ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρJ : |overlap x y| ≤ 1/(2*(M+1)*J) :=
    (hρ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hactual:=hall N m hN x y hx hy e f he hf htanx htany hρr
  let A:=residualPairScore c x y e f
  have hA : Surjective A := hactual.2.2.2.2.1
  refine ⟨hA,?_⟩
  intro w
  have hErr : ‖gram A-gram B‖ ≤ J*|overlap x y|^μ.minDegree := by
    have hh:=residualPairScore_gram_reference_bound hN μ hQ.le (by omega) x y hx hy e f he hf
      htanx htany hρ1 (show 0 ≤ 1/δ by positivity) hactual.2.1 hactual.2.2.1
    convert hh using 1
    dsimp only [J,L]
    ring
  have hp : |overlap x y|^μ.minDegree ≤ |overlap x y| := by
    simpa only [pow_one] using pow_le_pow_of_le_one (abs_nonneg _) hρ1 (show 1 ≤ μ.minDegree by omega)
  have hsmall : M*‖gram A-gram B‖ ≤ 1/2 := by
    have hh:=(le_div_iff₀ (by positivity : 0 < 2*(M+1)*J)).mp hρJ
    have hbound : M*‖gram A-gram B‖ ≤ M*(J*|overlap x y|) := by
      exact mul_le_mul_of_nonneg_left (hErr.trans (mul_le_mul_of_nonneg_left hp hJ.le)) hM
    have hpos : 0 ≤ J*|overlap x y| := by positivity
    nlinarith
  have hlog:=gram_log_difference_le A hA B hB hsmall
  have hdim : Module.finrank ℝ ScorePairSpace=4 := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq,Module.finrank_prod]
    norm_num [finrank_euclideanSpace]
  rw [hdim] at hlog
  have hdet : |Real.log (gram A).det-Real.log (gram B).det| ≤ 8*M*J*|overlap x y|^μ.minDegree := by
    apply hlog.trans
    change 2*(4:ℝ)*M*‖gram A-gram B‖ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hErr (show 0 ≤ 8*M by positivity)]
  have hDensity:=log_density_ratio_bound A hA B hB w hdet
  calc
    _ ≤ (8*M*J*|overlap x y|^μ.minDegree)/2+
      ((1/δ)*(J*|overlap x y|^μ.minDegree)*T*‖w‖^2)/2 := by
      apply hDensity.trans
      gcongr
      exact hactual.2.2.2.2.2
    _ = (D+C*‖w‖^2)*|overlap x y|^μ.minDegree := by dsimp only [D,C];ring
    _ ≤ K*(1+‖w‖^2)*|overlap x y|^μ.minDegree := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [K]
      nlinarith [sq_nonneg ‖w‖,mul_nonneg hD (sq_nonneg ‖w‖)]

end
end SlowEquilibration.PairObservationSmallOverlap
