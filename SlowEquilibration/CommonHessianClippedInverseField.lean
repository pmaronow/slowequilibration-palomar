-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianBulkOperatorMeanSquare
public import SlowEquilibration.GOEClippedInverseOnGap
public import SlowEquilibration.GOEPhysicalPrefactors

/-! Actual common-bulk clipped inverse field and dimension-uniform
physical cutoff norm bound. No operator field or Hessian identification is
assumed: the field is the genuine Mathlib functional calculus. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity GaussianQuadraticVariance
open CanonicalGOERealization GOEAsymptotics GOEClippedResolvent GOEScaling GOEPhysicalPrefactors
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def unflattenMatrix (m : ℕ) (z : EuclideanSpace ℝ (CoefficientIndex m)) : Matrix (Fin m) (Fin m) ℝ :=
  gaussianToMatrix (flattenEquiv m z)

lemma unflattenMatrix_measurable (m : ℕ) : Measurable (unflattenMatrix m) :=
  (gaussianToMatrix_measurable m).comp (flattenEquiv m).continuous.measurable

lemma unflattenMatrix_actual_hessian {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (J : Disorder N P) :
    unflattenMatrix m (actualObservation (flatHessianCLM c x e) J)=hessianMatrix c x e J := by
  ext i j
  change actualObservation (flatHessianCLM c x e) J ⟨i,j⟩=jet c 2 x ![e i,e j] J
  exact flatHessianCLM_actualObservation c x e J ⟨i,j⟩

def commonClippedInverseField {m : ℕ} (k ρ : ℝ) (z : CommonBulkPairSpace m) :
    EuclideanSpace ℝ (Fin m)→L[ℝ]EuclideanSpace ℝ (Fin m) :=
  clippedInverseOperator k ρ (unflattenMatrix m z.fst)

lemma commonClippedInverseField_measurable (m : ℕ) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Measurable (commonClippedInverseField (m:=m) k ρ) :=
  (clippedInverseOperator_measurable m k hρ).comp ((unflattenMatrix_measurable m).comp
    (show Measurable (fun z:CommonBulkPairSpace m=>z.fst) from by fun_prop))

lemma commonClippedInverseField_symmetric {m : ℕ} (k ρ : ℝ) (z : CommonBulkPairSpace m) :
    (commonClippedInverseField k ρ z).toLinearMap.IsSymmetric :=
  clippedInverseOperator_symmetric k ρ _

lemma commonClippedInverseField_norm_le {m : ℕ} (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : CommonBulkPairSpace m) :
    ‖commonClippedInverseField k ρ z‖ ≤ ρ⁻¹ :=
  clippedInverseOperator_norm_le k hρ _

/-- This is the literal clipped inverse of the first actual common Hessian
in the same original tensor sample, rather than an abstract bulk operator. -/
lemma commonClippedInverseField_actual {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e : Fin m → Vector N) (J : Disorder N P) (k ρ : ℝ) :
    commonClippedInverseField k ρ
      (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)) J)=
      clippedInverseOperator k ρ (hessianMatrix c x e J) := by
  change clippedInverseOperator k ρ
    (unflattenMatrix m (actualObservation (flatHessianCLM c x e) J))=_
  rw [unflattenMatrix_actual_hessian]

/-- Dimension-uniform actual operator norm at the explicit physical
cutoff a_N*rho; no norm bound or spectral event is supplied as a premise. -/
theorem physical_commonClippedInverseField_norm_le (n j : ℕ) {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (k : ℝ) (z : CommonBulkPairSpace (n+1)) :
    ‖commonClippedInverseField k (scaleFactor n (n+1+j) b*ρ) z‖ ≤
      (Real.sqrt (b/(j+1:ℝ))*ρ)⁻¹ := by
  have ha : 0 < scaleFactor n (n+1+j) b:=scaleFactor_pos n (by omega) hb
  have hl : 0 < Real.sqrt (b/(j+1:ℝ)):=Real.sqrt_pos.mpr (by positivity)
  calc
    _ ≤ (scaleFactor n (n+1+j) b*ρ)⁻¹:=commonClippedInverseField_norm_le k (mul_pos ha hρ) z
    _ ≤ _ := (inv_le_inv₀ (mul_pos ha hρ) (mul_pos hl hρ)).mpr
      (mul_le_mul_of_nonneg_right (scaleFactor_lower n j hb.le) hρ.le)

end
end SlowEquilibration.SphericalCommonHessianRegression

