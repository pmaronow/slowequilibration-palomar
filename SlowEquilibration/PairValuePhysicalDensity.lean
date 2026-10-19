-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityDilation
public import SlowEquilibration.PairValueDensityFactorization

/-! Proper energy-only pair densities with the genuine Jacobian N. The
one-point physical height factors are sqrt N, so their product cancels N
exactly in the relative intensity. No four-mark pure density is introduced. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory GaussianRegression SphericalModel SphericalGaussianJet
open WholeFieldRegression
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma valuePairSpace_finrank : Module.finrank ℝ ValuePairSpace=2 := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq,Module.finrank_prod]
  norm_num

/-- The actual residual normalized Gaussian value law, divided by sqrt N,
has a genuine Lebesgue density with Jacobian N. -/
theorem residualPairValue_physical_law_density {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (x y : Vector N) (e f : Fin m → Vector N)
    (hA : Surjective (residualPairValue c x y e f)) :
    (observationLaw (residualPairValue c x y e f)).map
      (fun w : ValuePairSpace=>(Real.sqrt (N:ℝ))⁻¹ • w)=
      volume.withDensity (fun h : ValuePairSpace=>ENNReal.ofReal (N:ℝ)*
        observationPdf (residualPairValue c x y e f) (Real.sqrt (N:ℝ) • h)) := by
  rw [observationLaw_eq_explicit_density _ hA]
  have h:=map_withDensity_div_smul (observationPdf (residualPairValue c x y e f))
    (observationPdf_measurable _) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  rw [valuePairSpace_finrank,Real.sq_sqrt (Nat.cast_nonneg N)] at h
  exact h

/-- The actual one-point spherical height law has Jacobian sqrt N.
The nondegeneracy follows from the genuine one-point value Gram. -/
theorem normalizedValue_physical_law_density {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (observationLaw (normalizedValue c x)).map
      (fun w : ℝ=>(Real.sqrt (N:ℝ))⁻¹*w)=
      volume.withDensity (fun h : ℝ=>ENNReal.ofReal (Real.sqrt (N:ℝ))*
        observationPdf (normalizedValue c x) (Real.sqrt (N:ℝ)*h)) := by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceValue μ Q) :=
    SphericalSequentialRegression.center_value_surjective μ hQ
      NormalizedObservationCoercivity.referencePoint
      (by simpa using NormalizedObservationCoercivity.referencePoint_norm_sq)
  have hGram : gram (normalizedValue c x)=gram (referenceValue μ Q) :=
    normalizedValue_gram_eq_reference hN μ hQ.le x hx
  have hA : Surjective (normalizedValue c x) :=
    surjective_of_gram_det_ne_zero _
      (by rw [hGram];exact (gram_det_pos _ hRef).ne')
  rw [observationLaw_eq_explicit_density _ hA]
  have h:=map_withDensity_div_smul (observationPdf (normalizedValue c x))
    (observationPdf_measurable _) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  simpa only [Module.finrank_self,pow_one,smul_eq_mul] using h

/-- Literal one-point physical height density, with Jacobian sqrt N. -/
def physicalValueDensity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : ℕ) (A : E →L[ℝ] ℝ) (h : ℝ) : ℝ :=
  Real.sqrt (N:ℝ)*realObservationDensity A (Real.sqrt (N:ℝ)*h)

/-- Literal two-point physical height density, with Jacobian N. -/
def physicalPairValueDensity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (N : ℕ) (A : E →L[ℝ] ValuePairSpace) (h1 h2 : ℝ) : ℝ :=
  (N:ℝ)*realObservationDensity A (valueScorePairTarget N h1 h2)

/-- The Jacobian cancellation is exact, before any asymptotic estimate. -/
lemma physical_pair_value_density_ratio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ} (hN : 0 < N)
    (A : E →L[ℝ] ValuePairSpace) (B C : E →L[ℝ] ℝ) (h1 h2 : ℝ) :
    physicalPairValueDensity N A h1 h2 /
      (physicalValueDensity N B h1*physicalValueDensity N C h2)=
      realObservationDensity A (valueScorePairTarget N h1 h2)/
        (realObservationDensity B (Real.sqrt (N:ℝ)*h1)*
          realObservationDensity C (Real.sqrt (N:ℝ)*h2)) := by
  unfold physicalPairValueDensity physicalValueDensity
  have hden : Real.sqrt (N:ℝ)*realObservationDensity B (Real.sqrt (N:ℝ)*h1)*
      (Real.sqrt (N:ℝ)*realObservationDensity C (Real.sqrt (N:ℝ)*h2))=
      (N:ℝ)*(realObservationDensity B (Real.sqrt (N:ℝ)*h1)*
        realObservationDensity C (Real.sqrt (N:ℝ)*h2)) := by
    calc
      _ = (Real.sqrt (N:ℝ))^2*(realObservationDensity B (Real.sqrt (N:ℝ)*h1)*
        realObservationDensity C (Real.sqrt (N:ℝ)*h2)) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hden,mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]

end
end SlowEquilibration.NormalizedPairObservations

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open SphericalModel SphericalGaussianJet NormalizedPairObservations
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The sharp proper-value density bound holds for actual physical densities,
including the N rather than N² pair Jacobian required by pure models. -/
theorem uniform_physical_value_density_ratio (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 h2 : ℝ,|h1| ≤ M → |h2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |Real.log (physicalPairValueDensity N (residualPairValue c x y e f) h1 h2 /
        (physicalValueDensity N (normalizedValue c x) h1*
          physicalValueDensity N (normalizedValue c y) h2))| ≤ K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_physical_pair_value_density μ hQ hdeg M hM
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 h2 hh1 hh2
  dsimp only
  rw [physical_pair_value_density_ratio hN]
  exact hall N m hN x y hx hy e f he hf htanx htany hρ h1 h2 hh1 hh2

end
end SlowEquilibration.PairObservationSmallOverlap
