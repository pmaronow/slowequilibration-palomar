-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEAsymptotics
public import SlowEquilibration.SymmetricGaussianRealization

/-! Actual finite GOE as a bounded symmetric linear image of the genuine
standard Gaussian coefficient law. Normalization is literal b/N, with no
spectral or covariance-law conclusion assumed. -/

@[expose] public section
namespace SlowEquilibration.CanonicalGOERealization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open GOEAsymptotics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev CoefficientIndex (m : ℕ) := Sigma (fun _ : Fin m => Fin m)

def flattenEquiv (m : ℕ) : EuclideanSpace ℝ (CoefficientIndex m) ≃ₗᵢ[ℝ] GaussianMatrix m :=
  LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : Fin m => fun _ : Fin m => ℝ)

def realization (m N : ℕ) (b : ℝ) : EuclideanSpace ℝ (CoefficientIndex m) →L[ℝ] GaussianMatrix m :=
  Real.sqrt (2*b/(N:ℝ)) • (SymmetricGaussianRealization.symmetrize.comp
    (flattenEquiv m).toContinuousLinearEquiv.toContinuousLinearMap)

lemma realization_symmetric (m N : ℕ) (b : ℝ) :
    ∀ z i j,realization m N b z i j=realization m N b z j i := by
  intro z i j
  change Real.sqrt (2*b/(N:ℝ))*(SymmetricGaussianRealization.symmetrize (flattenEquiv m z) i j)=
    Real.sqrt (2*b/(N:ℝ))*(SymmetricGaussianRealization.symmetrize (flattenEquiv m z) j i)
  rw [SymmetricGaussianRealization.symmetrize_symmetric]

lemma realization_norm_le (m N : ℕ) (b : ℝ) :
    ‖realization m N b‖≤Real.sqrt (2*b/(N:ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  change ‖Real.sqrt (2*b/(N:ℝ)) • SymmetricGaussianRealization.symmetrize (flattenEquiv m z)‖≤_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (SymmetricGaussianRealization.symmetrize_norm_le _)
    (Real.sqrt_nonneg _)).trans_eq (by rw [LinearIsometryEquiv.norm_map])

lemma realization_eq (m N : ℕ) (b : ℝ) :
    (realization m N b : EuclideanSpace ℝ (CoefficientIndex m) → GaussianMatrix m)=
      (OAI.CriticalSK.symmetrizeGaussianMatrix (Real.sqrt (2*b/(N:ℝ))/2)) ∘ flattenEquiv m := by
  funext z
  ext i j
  dsimp only [Function.comp_apply]
  change Real.sqrt (2*b/(N:ℝ))*(SymmetricGaussianRealization.symmetrize (flattenEquiv m z) i j)=
    (OAI.CriticalSK.symmetrizeGaussianMatrix (Real.sqrt (2*b/(N:ℝ))/2) (flattenEquiv m z)) i j
  rw [SymmetricGaussianRealization.symmetrize_apply]
  change Real.sqrt (2*b/(N:ℝ))*((flattenEquiv m z i j+flattenEquiv m z j i)/2)=
    (Real.sqrt (2*b/(N:ℝ))/2)*(flattenEquiv m z i j+flattenEquiv m z j i)
  ring

/-- The actual explicit upper-triangle product Gaussian GOE agrees exactly
with this actual linear image of independent standard Gaussian coefficients. -/
theorem realization_hasLaw (m : ℕ) {N : ℕ} (hN : 0<N) {b : ℝ} (hb : 0≤b) :
    HasLaw (realization m N b)
      ((SphericalGaussianJet.goeLaw m N b).map matrixToGaussian)
      (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex m)) := by
  refine ⟨(realization m N b).continuous.measurable.aemeasurable,?_⟩
  have hscale : 2*(Real.sqrt (2*b/(N:ℝ))/2)^2=b/(N:ℝ) := by
    have hs := Real.sq_sqrt (show 0≤2*b/(N:ℝ) by positivity)
    calc
      _=Real.sqrt (2*b/(N:ℝ))^2/2 := by ring
      _=b/(N:ℝ) := by rw [hs];ring
  rw [goeLaw_bridge m N b _ hscale]
  have hstd : SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex m)=
      stdGaussian (EuclideanSpace ℝ (CoefficientIndex m)) := map_pi_eq_stdGaussian
  rw [hstd,realization_eq]
  rw [← Measure.map_map (OAI.CriticalSK.symmetrizeGaussianMatrix_continuous _).measurable
    (flattenEquiv m).continuous.measurable,stdGaussian_map (flattenEquiv m)]
  rfl

/-- Matrix-valued version under the manuscript's literal GOE law. -/
theorem matrix_realization_hasLaw (m : ℕ) {N : ℕ} (hN : 0<N) {b : ℝ} (hb : 0≤b) :
    HasLaw (fun z => gaussianToMatrix (realization m N b z)) (SphericalGaussianJet.goeLaw m N b)
      (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex m)) := by
  have hG : HasLaw (gaussianToMatrix (k := m))
      (((SphericalGaussianJet.goeLaw m N b).map matrixToGaussian).map gaussianToMatrix)
      ((SphericalGaussianJet.goeLaw m N b).map matrixToGaussian) :=
    ⟨(gaussianToMatrix_measurable m).aemeasurable,rfl⟩
  have hh := hG.comp (realization_hasLaw m hN hb)
  have he : ((SphericalGaussianJet.goeLaw m N b).map matrixToGaussian).map gaussianToMatrix=
      SphericalGaussianJet.goeLaw m N b := by
    rw [Measure.map_map (gaussianToMatrix_measurable m) (matrixToGaussian_measurable m)]
    change (SphericalGaussianJet.goeLaw m N b).map id=_
    exact Measure.map_id
  rw [he] at hh
  exact hh

end
end SlowEquilibration.CanonicalGOERealization
