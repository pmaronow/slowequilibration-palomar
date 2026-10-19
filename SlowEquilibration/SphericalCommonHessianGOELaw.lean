-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCommonHessianGram
public import SlowEquilibration.GaussianMapGramIdentity
public import SlowEquilibration.SecondCovarianceCorrelation

/-! Identification of the actual common-complement joint Hessian law with
an actual canonical correlated GOE realization. The original tensor model
and the explicit independent Gaussian GOE provider supply the marginal law. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalHessianTraceCovariance
open SphericalConditionalMatrices SphericalTwoPointCovariance CanonicalGOERealization GOEAsymptotics
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def flatMatrix (m : ℕ) (W : Matrix (Fin m) (Fin m) ℝ) : EuclideanSpace ℝ (CoefficientIndex m) :=
  (flattenEquiv m).symm (matrixToGaussian W)

lemma flatMatrix_measurable (m : ℕ) : Measurable (flatMatrix m) :=
  (flattenEquiv m).symm.continuous.measurable.comp (matrixToGaussian_measurable m)

def flatGOERealization (m N : ℕ) (b : ℝ) : EuclideanSpace ℝ (CoefficientIndex m) →L[ℝ] EuclideanSpace ℝ (CoefficientIndex m) :=
  ((flattenEquiv m).symm : GaussianMatrix m →L[ℝ] EuclideanSpace ℝ (CoefficientIndex m)).comp
    (CanonicalGOERealization.realization m N b)

lemma flatGOERealization_law (m : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    (stdGaussian (EuclideanSpace ℝ (CoefficientIndex m))).map (flatGOERealization m N b)=
      (goeLaw m N b).map (flatMatrix m) := by
  have h:= (hasLaw_map (flatMatrix_measurable m).aemeasurable).fun_comp
    (matrix_realization_hasLaw m hN hb)
  have hstd : SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex m)=
      stdGaussian (EuclideanSpace ℝ (CoefficientIndex m)) := map_pi_eq_stdGaussian
  change (stdGaussian (EuclideanSpace ℝ (CoefficientIndex m))).map
    (fun z => (flattenEquiv m).symm (CanonicalGOERealization.realization m N b z))=_
  simpa only [hstd,Function.comp_def,flatMatrix,matrixToGaussian_gaussianToMatrix] using h.map_eq

/-- Complete actual one-point Hessian pushforward, with its genuine finite
GOE law, before comparing any conditional pair law. -/
lemma flatHessianCLM_law {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0) :
    (stdGaussian (EuclideanDisorder N P)).map (flatHessianCLM c x e)=
      (goeLaw m N (secondCovariance c 1)).map (flatMatrix m) := by
  have hH:= (hasLaw_map (flatMatrix_measurable m).aemeasurable).fun_comp
    (tangent_hessian_matrix_hasLaw (r:=1) hN c hc x (by simpa using hx) e he htanx)
  have hH' : HasLaw (actualObservation (flatHessianCLM c x e))
      ((goeLaw m N (secondCovariance c 1)).map (flatMatrix m)) (disorderLaw N P) := by
    apply hH.congr
    apply Filter.Eventually.of_forall
    intro J
    apply PiLp.ext
    intro i
    simp only [flatHessianCLM_actualObservation,flatMatrix,flattenEquiv,
      LinearIsometryEquiv.piLpCurry_symm_apply,PiLp.toLp_apply]
    rfl
  have hG:= (hasLaw_map (flatHessianCLM c x e).continuous.measurable.aemeasurable).fun_comp
    (actual_flattened_gaussian N P)
  exact hG.map_eq.symm.trans hH'.map_eq

/-- Exact comparison of the actual tensor covariance with the canonical
GOE covariance is derived from their actual complete marginal laws. -/
lemma flatHessianCLM_gram_eq_GOE {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htanx : ∀ i,inner ℝ (e i) x=0)
    (hb : 0 ≤ secondCovariance c 1) :
    gram (flatHessianCLM c x e)=gram (flatGOERealization m N (secondCovariance c 1)) := by
  apply gram_eq_of_gaussian_map_eq
  rw [flatHessianCLM_law hN c hc x hx e he htanx,flatGOERealization_law m hN hb]

/-- Actual unconditioned two-point bulk law equals the canonical correlated
GOE law; neither its covariance nor its GOE law is assumed. -/
theorem common_flat_hessian_pair_GOE_law {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hb : 0 < secondCovariance c 1) (hr : |overlap x y| ≤ 1) :
    (stdGaussian (EuclideanDisorder N P)).map
      (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))=
      (stdGaussian (WithLp 2 (EuclideanSpace ℝ (CoefficientIndex m)×EuclideanSpace ℝ (CoefficientIndex m)))).map
        (correlatedPair (flatGOERealization m N (secondCovariance c 1))
          (hessianCorrelation c (overlap x y)) (hessianIndependentScale c (overlap x y))) := by
  have hGram:=flatHessianCLM_gram_eq_GOE hN c hc x hx e he htanx hb.le
  apply gaussian_pair_law_eq_correlated _ _ _ _ _ (hessianCorrelation_rotation c hc hb hr) hGram
    ((flatHessianCLM_gram_eq hN c hc x y hx hy e he htanx htany).trans hGram)
  rw [flatHessianCLM_cross_gram hN c hc x y hx e he htanx htany hb.ne',hGram]
  rfl

end
end SlowEquilibration.SphericalCommonHessianRegression
