-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityDilation
public import SlowEquilibration.PairScoreDensityFactorization

/-! Actual mixed four-score physical density with Jacobian N² and genuine
one-point two-score density with Jacobian N. The two factors cancel exactly
in the relative pair intensity. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory GaussianRegression SphericalModel SphericalGaussianJet
open WholeFieldRegression NormalizedObservationCoercivity
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma scorePairSpace_finrank : Module.finrank ℝ ScorePairSpace=4 := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq,Module.finrank_prod]
  norm_num [finrank_euclideanSpace]

/-- The true residual four-score Gaussian divided by sqrt N has the genuine
physical Lebesgue density with Jacobian N². -/
theorem residualPairScore_physical_law_density {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (x y : Vector N) (e f : Fin m → Vector N)
    (hA : Surjective (residualPairScore c x y e f)) :
    (observationLaw (residualPairScore c x y e f)).map
      (fun w : ScorePairSpace=>(Real.sqrt (N:ℝ))⁻¹ • w)=
      volume.withDensity (fun h : ScorePairSpace=>ENNReal.ofReal ((N:ℝ)^2)*
        observationPdf (residualPairScore c x y e f) (Real.sqrt (N:ℝ) • h)) := by
  rw [observationLaw_eq_explicit_density _ hA]
  have h:=map_withDensity_div_smul (observationPdf (residualPairScore c x y e f))
    (observationPdf_measurable _) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  rw [scorePairSpace_finrank,show (4:ℕ)=2*2 by norm_num,pow_mul,
    Real.sq_sqrt (Nat.cast_nonneg N)] at h
  exact h

/-- The actual one-point mixed score law has Jacobian N. Its nondegeneracy
is proved from the true non-pure reference score Gram. -/
theorem normalizedScore_physical_law_density {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (observationLaw (normalizedScore c x)).map
      (fun w : EuclideanSpace ℝ (Fin 2)=>(Real.sqrt (N:ℝ))⁻¹ • w)=
      volume.withDensity (fun h : EuclideanSpace ℝ (Fin 2)=>ENNReal.ofReal (N:ℝ)*
        observationPdf (normalizedScore c x) (Real.sqrt (N:ℝ) • h)) := by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceScore μ Q) :=
    center_score_surjective (by norm_num) μ hQ hnp referencePoint
      (by simpa using referencePoint_norm_sq)
  have hGram : gram (normalizedScore c x)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ.le x hx
  have hA : Surjective (normalizedScore c x) :=
    surjective_of_gram_det_ne_zero _ (by rw [hGram];exact (gram_det_pos _ hRef).ne')
  rw [observationLaw_eq_explicit_density _ hA]
  have h:=map_withDensity_div_smul (observationPdf (normalizedScore c x))
    (observationPdf_measurable _) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))=2 := by
    norm_num [finrank_euclideanSpace]
  rw [hdim,Real.sq_sqrt (Nat.cast_nonneg N)] at h
  exact h

def physicalScoreTarget (N : ℕ) (h k : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.sqrt (N:ℝ)*h,Real.sqrt (N:ℝ)*k]

/-- Literal one-point physical height/radial-score density, Jacobian N. -/
def physicalScoreDensity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : ℕ) (A : E →L[ℝ] EuclideanSpace ℝ (Fin 2)) (h k : ℝ) : ℝ :=
  (N:ℝ)*realObservationDensity A (physicalScoreTarget N h k)

/-- Literal physical four-mark pair density, Jacobian N². -/
def physicalPairScoreDensity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : ℕ) (A : E →L[ℝ] ScorePairSpace) (h1 k1 h2 k2 : ℝ) : ℝ :=
  (N:ℝ)^2*realObservationDensity A (scorePairTarget N h1 k1 h2 k2)

/-- Both one-point Jacobians cancel the pair Jacobian exactly. -/
lemma physical_pair_score_density_ratio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ} (hN : 0 < N)
    (A : E →L[ℝ] ScorePairSpace) (B C : E →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (h1 k1 h2 k2 : ℝ) :
    physicalPairScoreDensity N A h1 k1 h2 k2 /
      (physicalScoreDensity N B h1 k1*physicalScoreDensity N C h2 k2)=
      realObservationDensity A (scorePairTarget N h1 k1 h2 k2)/
        (realObservationDensity B (physicalScoreTarget N h1 k1)*
          realObservationDensity C (physicalScoreTarget N h2 k2)) := by
  unfold physicalPairScoreDensity physicalScoreDensity
  have hden : (N:ℝ)*realObservationDensity B (physicalScoreTarget N h1 k1)*
      ((N:ℝ)*realObservationDensity C (physicalScoreTarget N h2 k2))=
      (N:ℝ)^2*(realObservationDensity B (physicalScoreTarget N h1 k1)*
        realObservationDensity C (physicalScoreTarget N h2 k2)) := by ring
  rw [hden,mul_div_mul_left _ _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)))]

end
end SlowEquilibration.NormalizedPairObservations

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open SphericalModel SphericalGaussianJet NormalizedPairObservations
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual mixed physical densities obey the sharp source log bound,
with their N² pair Jacobian and both N one-point Jacobians retained. -/
theorem uniform_physical_score_density_ratio (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 k1 h2 k2 : ℝ,|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |Real.log (physicalPairScoreDensity N (residualPairScore c x y e f) h1 k1 h2 k2 /
        (physicalScoreDensity N (normalizedScore c x) h1 k1*
          physicalScoreDensity N (normalizedScore c y) h2 k2))| ≤ K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_physical_pair_score_density μ hQ hnp hdeg M hM
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 k1 h2 k2 hh1 hk1 hh2 hk2
  dsimp only
  rw [physical_pair_score_density_ratio hN]
  exact hall N m hN x y hx hy e f he hf htanx htany hρ h1 k1 h2 k2 hh1 hk1 hh2 hk2

end
end SlowEquilibration.PairObservationSmallOverlap
