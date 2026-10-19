-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCommonHessianCovariance
public import SlowEquilibration.SphericalCommonHessianRegression
public import SlowEquilibration.CanonicalGOERealization
public import SlowEquilibration.GaussianCorrelatedPairLaw

/-! Actual common-complement Hessian Gram operators and their genuine
correlated Gaussian joint law, derived from the fourth-jet covariance. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalHessianTraceCovariance
open SphericalPairRegression SphericalTwoPointCovariance CanonicalGOERealization
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def flatHessianCLM {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (CoefficientIndex m) :=
  ((flattenEquiv m).symm : GOEAsymptotics.GaussianMatrix m →L[ℝ] EuclideanSpace ℝ (CoefficientIndex m)).comp
    (hessianGaussianCLM c x e)

lemma flatHessianCLM_apply {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) (i : CoefficientIndex m) :
    flatHessianCLM c x e g i=jet c 2 x ![e i.1,e i.2] (unpackDisorder g) := by
  simp only [flatHessianCLM,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',flattenEquiv,
    LinearIsometryEquiv.piLpCurry_symm_apply,PiLp.toLp_apply]
  simp only [hessianGaussianCLM_apply,hessianEntry]
  rfl

lemma flatHessianCLM_actualObservation {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (J : Disorder N P) (i : CoefficientIndex m) :
    actualObservation (flatHessianCLM c x e) J i=jet c 2 x ![e i.1,e i.2] J := by
  simp only [actualObservation,flatHessianCLM_apply,unpack_euclideanDisorder]

/-- Exact marginal Gram equality follows from both actual sphere points
and the same orthonormal common frame; no covariance equality is assumed. -/
theorem flatHessianCLM_gram_eq {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0) :
    gram (flatHessianCLM c y e)=gram (flatHessianCLM c x e) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (CoefficientIndex m) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have hX:=actual_covariance_gram (flatHessianCLM c x e) i j
  have hY:=actual_covariance_gram (flatHessianCLM c y e) i j
  simp only [flatHessianCLM_actualObservation] at hX hY
  change cov[hessianEntry c x e i.1 i.2,hessianEntry c x e j.1 j.2;disorderLaw N P]=_ at hX
  change cov[hessianEntry c y e i.1 i.2,hessianEntry c y e j.1 j.2;disorderLaw N P]=_ at hY
  rw [hessianEntry_covariance (r:=1) hN c hc x (by simpa using hx) e he htanx] at hX
  rw [hessianEntry_covariance (r:=1) hN c hc y (by simpa using hy) e he htany] at hY
  exact hY.symm.trans hX

/-- Literal actual cross Gram equals σ times the actual one-point Gram.
The potentially antisymmetric matrix directions remain present and singular. -/
theorem flatHessianCLM_cross_gram {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hb : secondCovariance c 1≠0) :
    (flatHessianCLM c x e).comp (flatHessianCLM c y e).adjoint=
      (secondCovariance c (overlap x y)/secondCovariance c 1) • gram (flatHessianCLM c x e) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (CoefficientIndex m) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have hXY:=cross_covariance_entry (flatHessianCLM c x e) (flatHessianCLM c y e) i j
  have hX:=actual_covariance_gram (flatHessianCLM c x e) i j
  simp only [flatHessianCLM_actualObservation] at hXY hX
  rw [common_hessian_covariance hN c hc x y _ _ _ _ (htany i.1) (htany i.2)] at hXY
  simp only [orthonormal_iff_ite.mp he] at hXY
  change cov[hessianEntry c x e i.1 i.2,hessianEntry c x e j.1 j.2;disorderLaw N P]=_ at hX
  rw [hessianEntry_covariance (r:=1) hN c hc x (by simpa using hx) e he htanx] at hX
  change flatHessianCLM c x e ((flatHessianCLM c y e).adjoint (EuclideanSpace.basisFun (CoefficientIndex m) ℝ j)) i=
    (secondCovariance c (overlap x y)/secondCovariance c 1)*
      gram (flatHessianCLM c x e) (EuclideanSpace.basisFun (CoefficientIndex m) ℝ j) i
  rw [← hXY,← hX]
  field_simp

/-- Complete actual unconditioned bulk pair law is the true correlated pair
of independent copies of the actual one-point Hessian. The covariance law
is derived from the tensor field, including its matrix singular directions. -/
theorem common_flat_hessian_pair_law {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hb : secondCovariance c 1≠0) (s : ℝ)
    (hrot : (secondCovariance c (overlap x y)/secondCovariance c 1)^2+s^2=1) :
    (stdGaussian (EuclideanDisorder N P)).map
      (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e))=
      (stdGaussian (WithLp 2 (EuclideanDisorder N P×EuclideanDisorder N P))).map
        (correlatedPair (flatHessianCLM c x e) (secondCovariance c (overlap x y)/secondCovariance c 1) s) := by
  apply gaussian_pair_law_eq_correlated _ _ _ _ _ hrot rfl
    (flatHessianCLM_gram_eq hN c hc x y hx hy e he htanx htany)
  exact flatHessianCLM_cross_gram hN c hc x y hx e he htanx htany hb

end
end SlowEquilibration.SphericalCommonHessianRegression
