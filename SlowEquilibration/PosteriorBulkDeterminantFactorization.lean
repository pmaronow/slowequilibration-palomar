-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorCommonGOE
public import SlowEquilibration.CanonicalGOECoordinates

/-! Raw common-complement determinant factorization under the actual
full-tensor posterior, using the proved canonical correlated Gaussian law. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedPairObservations SphericalTwoPointCovariance
open CanonicalGOERealization CanonicalGOECoordinates GOEAsymptotics GOEDeterminantMoments GOEPhysicalPotential
open GOERawMoments CorrelatedGOEDeterminants OAI.MinUncut.GaussianHermite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def flatNormalizedDeterminant (n N : ℕ) (b k : ℝ) (z : EuclideanSpace ℝ (CoefficientIndex (n+1))) : ℝ :=
  matrixAbsoluteDet n k (gaussianToMatrix (flattenEquiv (n+1) z))/physicalMean n N b k

def flatNormalizedProduct (n N : ℕ) (b k1 k2 : ℝ)
    (w : WithLp 2 (EuclideanSpace ℝ (CoefficientIndex (n+1))×EuclideanSpace ℝ (CoefficientIndex (n+1)))) : ℝ :=
  flatNormalizedDeterminant n N b k1 w.fst*flatNormalizedDeterminant n N b k2 w.snd

lemma flatNormalizedDeterminant_measurable (n N : ℕ) (b k : ℝ) :
    Measurable (flatNormalizedDeterminant n N b k) :=
  (((matrixAbsoluteDet_measurable n k).comp ((gaussianToMatrix_measurable (n+1)).comp
    (flattenEquiv (n+1)).continuous.measurable))).div_const _

lemma flatNormalizedProduct_measurable (n N : ℕ) (b k1 k2 : ℝ) :
    Measurable (flatNormalizedProduct n N b k1 k2) :=
  ((flatNormalizedDeterminant_measurable n N b k1).comp (WithLp.fstL 2 ℝ _ _).continuous.measurable).mul
    ((flatNormalizedDeterminant_measurable n N b k2).comp (WithLp.sndL 2 ℝ _ _).continuous.measurable)

lemma flat_normalized_eq_coordinates (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) (k : ℝ) (z : Coordinates n) :
    flatNormalizedDeterminant n (n+1+j) b k
      (flatGOERealization (n+1) (n+1+j) b (WithLp.toLp 2 z))=
      normalizedDeterminant n j b k z := by
  unfold flatNormalizedDeterminant flatGOERealization normalizedDeterminant
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',
    LinearIsometryEquiv.apply_symm_apply]
  rw [canonical_realization_eq_physical n j hb z]

lemma flat_product_eq_coordinates (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) (k1 k2 ρ s : ℝ)
    (z : Coordinates n×Coordinates n) :
    flatNormalizedProduct n (n+1+j) b k1 k2
      (correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s (rawPairToHilbert z))=
      normalizedDeterminant n j b k1 z.1*normalizedDeterminant n j b k2 (ρ • z.1+s • z.2) := by
  change flatNormalizedDeterminant n (n+1+j) b k1 (flatGOERealization (n+1) (n+1+j) b (WithLp.toLp 2 z.1))*
    flatNormalizedDeterminant n (n+1+j) b k2
      (ρ • flatGOERealization (n+1) (n+1+j) b (WithLp.toLp 2 z.1)+
        s • flatGOERealization (n+1) (n+1+j) b (WithLp.toLp 2 z.2))=_
  rw [← map_smul,← map_smul,← map_add,← WithLp.toLp_smul,← WithLp.toLp_smul,← WithLp.toLp_add,
    flat_normalized_eq_coordinates n j hb,flat_normalized_eq_coordinates n j hb]

/-- Genuine actual canonical bulk determinant expectation, with its actual
own mean normalizations, differs from one by O(|ρ|), uniformly in dimension. -/
theorem canonical_bulk_product_factorization (j : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C : ℝ,0 < C ∧ ∀ n : ℕ,∀ k1 k2 : ℝ,
      2*Real.sqrt b+g ≤ k1 → k1 ≤ Z → 2*Real.sqrt b+g ≤ k2 → k2 ≤ Z →
      ∀ ρ s : ℝ,ρ^2+s^2=1 → |ρ| ≤ 1 →
      let ν := (stdGaussian (WithLp 2 (EuclideanSpace ℝ (CoefficientIndex (n+1))×EuclideanSpace ℝ (CoefficientIndex (n+1))))).map
        (correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s)
      Integrable (flatNormalizedProduct n (n+1+j) b k1 k2) ν ∧
        |(∫ w,flatNormalizedProduct n (n+1+j) b k1 k2 w ∂ν)-1| ≤ C * |ρ| := by
  obtain ⟨C,hC,hall⟩:=normalized_correlated_goe_determinants j (Z:=Z) hb hg
  refine ⟨C,hC,?_⟩
  intro n k1 k2 hk1 hZ1 hk2 hZ2 ρ s hrot hρ
  dsimp only
  have h:=hall n k1 k2 hk1 hZ1 hk2 hZ2 ρ s hrot hρ
  have hmap : (stdGaussian (WithLp 2 (EuclideanSpace ℝ (CoefficientIndex (n+1))×EuclideanSpace ℝ (CoefficientIndex (n+1))))).map
      (correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s)=
      ((γpi (CoefficientIndex (n+1))).prod (γpi (CoefficientIndex (n+1)))).map
        ((correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s) ∘ rawPairToHilbert) := by
    rw [← independent_coordinates_law,Measure.map_map (by fun_prop) rawPairToHilbert_measurable]
  rw [hmap]
  constructor
  · exact (integrable_map_measure (flatNormalizedProduct_measurable n (n+1+j) b k1 k2).aestronglyMeasurable
      ((correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s).continuous.measurable.comp rawPairToHilbert_measurable).aemeasurable).mpr
      (by simpa only [Function.comp_def,flat_product_eq_coordinates n j hb.le] using h.1)
  · rw [integral_map (μ:=((γpi (CoefficientIndex (n+1))).prod (γpi (CoefficientIndex (n+1))))) ((correlatedPair (flatGOERealization (n+1) (n+1+j) b) ρ s).continuous.measurable.comp rawPairToHilbert_measurable).aemeasurable
      (flatNormalizedProduct_measurable n (n+1+j) b k1 k2).aestronglyMeasurable]
    simpa only [Function.comp_def,flat_product_eq_coordinates n j hb.le] using h.2

/-- Actual mixed posterior bulk determinant factorization at every target.
The common-complement GOE law is derived from the actual original tensor model. -/
theorem posterior_bulk_product_mixed_factorization {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    {g Z : ℝ} (hb : 0 < secondCovariance c 1) (hg : 0 < g) (j : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ n k : ℕ,∀ x y : Vector (n+1+j),
      ‖x‖^2=(n+1+j:ℕ) → ‖y‖^2=(n+1+j:ℕ) →
      ∀ e : Fin (n+1) → Vector (n+1+j),Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) →
      |overlap x y| ≤ 1 →
      ∀ f f' : Fin k → Vector (n+1+j),
      ∀ w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k),
      Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y f')) →
      ∀ k1 k2 : ℝ,2*Real.sqrt (secondCovariance c 1)+g ≤ k1 → k1 ≤ Z →
      2*Real.sqrt (secondCovariance c 1)+g ≤ k2 → k2 ≤ Z →
      let ν := coefficientKernel (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y f')) w
      let F := fun J : Disorder (n+1+j) P => flatNormalizedProduct n (n+1+j) (secondCovariance c 1) k1 k2
        (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)) J)
      Integrable F ν ∧ |(∫ J,F J ∂ν)-1| ≤ C * |hessianCorrelation c (overlap x y)| := by
  obtain ⟨C,hC,hall⟩:=canonical_bulk_product_factorization j (Z:=Z) hb hg
  refine ⟨C,hC,?_⟩
  intro n k x y hx hy e he htanx htany hr f f' w hA k1 k2 hk1 hZ1 hk2 hZ2
  dsimp only
  have hLaw:=posterior_common_GOE_mixed_hasLaw (by omega) c hc hdeg x y hx hy e he htanx htany hb hr f f' w hA
  have h:=hall n k1 k2 hk1 hZ1 hk2 hZ2 (hessianCorrelation c (overlap x y))
    (hessianIndependentScale c (overlap x y)) (hessianCorrelation_rotation c hc hb hr)
    (hessianCorrelation_abs_le_one c hc hb hr)
  dsimp only at h
  constructor
  · exact hLaw.integrable_fun_comp h.1
  · rw [← hLaw.integral_comp (flatNormalizedProduct_measurable n (n+1+j) (secondCovariance c 1) k1 k2).aestronglyMeasurable] at h
    exact h.2

/-- Actual proper value-only posterior bulk determinant factorization at every target.
The common-complement GOE law is derived from the actual original tensor model. -/
theorem posterior_bulk_product_value_factorization {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    {g Z : ℝ} (hb : 0 < secondCovariance c 1) (hg : 0 < g) (j : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ n k : ℕ,∀ x y : Vector (n+1+j),
      ‖x‖^2=(n+1+j:ℕ) → ‖y‖^2=(n+1+j:ℕ) →
      ∀ e : Fin (n+1) → Vector (n+1+j),Orthonormal ℝ e →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (e i) y=0) →
      |overlap x y| ≤ 1 →
      ∀ f f' : Fin k → Vector (n+1+j),
      ∀ w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k),
      Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y f')) →
      ∀ k1 k2 : ℝ,2*Real.sqrt (secondCovariance c 1)+g ≤ k1 → k1 ≤ Z →
      2*Real.sqrt (secondCovariance c 1)+g ≤ k2 → k2 ≤ Z →
      let ν := coefficientKernel (pairHilbert (singleValueObservation c x f) (singleValueObservation c y f')) w
      let F := fun J : Disorder (n+1+j) P => flatNormalizedProduct n (n+1+j) (secondCovariance c 1) k1 k2
        (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)) J)
      Integrable F ν ∧ |(∫ J,F J ∂ν)-1| ≤ C * |hessianCorrelation c (overlap x y)| := by
  obtain ⟨C,hC,hall⟩:=canonical_bulk_product_factorization j (Z:=Z) hb hg
  refine ⟨C,hC,?_⟩
  intro n k x y hx hy e he htanx htany hr f f' w hA k1 k2 hk1 hZ1 hk2 hZ2
  dsimp only
  have hLaw:=posterior_common_GOE_value_hasLaw (by omega) c hc hdeg x y hx hy e he htanx htany hb hr f f' w hA
  have h:=hall n k1 k2 hk1 hZ1 hk2 hZ2 (hessianCorrelation c (overlap x y))
    (hessianIndependentScale c (overlap x y)) (hessianCorrelation_rotation c hc hb hr)
    (hessianCorrelation_abs_le_one c hc hb hr)
  dsimp only at h
  constructor
  · exact hLaw.integrable_fun_comp h.1
  · rw [← hLaw.integral_comp (flatNormalizedProduct_measurable n (n+1+j) (secondCovariance c 1) k1 k2).aestronglyMeasurable] at h
    exact h.2

end
end SlowEquilibration.SphericalCommonHessianRegression
