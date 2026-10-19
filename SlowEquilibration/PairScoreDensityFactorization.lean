-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairResidualScoreDensity
public import SlowEquilibration.PairObservationTargets

/-! Actual pair-score density comparison with the product of its literal
one-point densities, including the physical sqrt N score targets. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedObservationCoercivity PairObservationTargets
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma referenceScorePair_density_eq_actual_marginals {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (w : ScorePairSpace) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    realObservationDensity (referenceScorePair μ Q) w=
      realObservationDensity (normalizedScore c x) w.fst*realObservationDensity (normalizedScore c y) w.snd := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceScore μ Q) :=
    center_score_surjective (by norm_num) μ hQ hnp referencePoint (by simpa using referencePoint_norm_sq)
  have hxGram : gram (normalizedScore c x)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ.le x hx
  have hyGram : gram (normalizedScore c y)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ.le y hy
  have hA : Surjective (normalizedScore c x) :=
    surjective_of_gram_det_ne_zero _ (by rw [hxGram];exact (gram_det_pos _ hRef).ne')
  have hB : Surjective (normalizedScore c y) :=
    surjective_of_gram_det_ne_zero _ (by rw [hyGram];exact (gram_det_pos _ hRef).ne')
  rw [referenceScorePair,realObservationDensity_independentPair _ hRef _ hRef,
    ← realObservationDensity_eq_of_gram _ hA _ hRef hxGram,
    ← realObservationDensity_eq_of_gram _ hB _ hRef hyGram]

def scorePairTarget (N : ℕ) (h1 k1 h2 k2 : ℝ) : ScorePairSpace :=
  WithLp.toLp 2 (WithLp.toLp 2 ![Real.sqrt (N:ℝ)*h1,Real.sqrt (N:ℝ)*k1],
    WithLp.toLp 2 ![Real.sqrt (N:ℝ)*h2,Real.sqrt (N:ℝ)*k2])

lemma scorePairTarget_norm_le (N : ℕ) {M h1 k1 h2 k2 : ℝ}
    (hh1 : |h1| ≤ M) (hk1 : |k1| ≤ M) (hh2 : |h2| ≤ M) (hk2 : |k2| ≤ M) :
    ‖scorePairTarget N h1 k1 h2 k2‖ ≤ 4*M*Real.sqrt (N:ℝ) := by
  have hfst:=WithLp.norm_fst_le _ (mixedGroupingEquiv 0 (mixedPairTarget N 0 h1 k1 h2 k2))
  rw [LinearIsometryEquiv.norm_map] at hfst
  exact hfst.trans (mixedPairTarget_norm_le N 0 hh1 hk1 hh2 hk2)

end
end SlowEquilibration.NormalizedPairObservations

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The actual conditional score density divided by both actual marginal
score densities has the source O(N|overlap|^d) error on every bounded mark box. -/
theorem uniform_physical_pair_score_density (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 k1 h2 k2 : ℝ,|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let w:=scorePairTarget N h1 k1 h2 k2
      |Real.log (realObservationDensity (residualPairScore c x y e f) w /
        (realObservationDensity (normalizedScore c x) w.fst*realObservationDensity (normalizedScore c y) w.snd))| ≤
          K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_residual_pair_score_density μ hQ hnp hdeg
  refine ⟨ρ0,K*(1+16*M^2),hρ0,by positivity,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 k1 h2 k2 hh1 hk1 hh2 hk2
  let w:=scorePairTarget N h1 k1 h2 k2
  have h:= (hall N m hN x y hx hy e f he hf htanx htany hρ).2 w
  rw [referenceScorePair_density_eq_actual_marginals hN μ hQ hnp x y hx hy w] at h
  have hn : ‖w‖ ≤ 4*M*Real.sqrt (N:ℝ) := scorePairTarget_norm_le N hh1 hk1 hh2 hk2
  have hs : ‖w‖^2 ≤ 16*M^2*(N:ℝ) := by
    have hh:=(sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4*M*Real.sqrt (N:ℝ))).mpr hn
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hh
    norm_num at hh
    exact hh
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  apply h.trans
  have hh:=mul_le_mul_of_nonneg_left (show 1+‖w‖^2 ≤ (1+16*M^2)*(N:ℝ) by nlinarith) hK.le
  exact mul_le_mul_of_nonneg_right (by convert hh using 1; ring) (by positivity)

end
end SlowEquilibration.PairObservationSmallOverlap
