-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCommonHessianRegression
public import SlowEquilibration.SphericalPairPlaneDirection
public import SlowEquilibration.NormalizedObservationBlocks

/-! Actual common-row Hessian couplings used in the one-border posterior
split. These are coefficient-linear observations of the original tensor field. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedPairObservations SphericalTwoPointCovariance
open ScalarCoefficientCovariance HessianObservationCovariance SphericalPairCommonFrame
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def commonRowCLM {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : Vector N) : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  jetFamilyCLM c (fun _=>2) (fun _=>x) (fun i=>![e i,v])

@[simp] lemma commonRowCLM_apply {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : Vector N) (g : EuclideanDisorder N P) (i : Fin m) :
    commonRowCLM c x e v g i=flatJetCLM c 2 x ![e i,v] g := by
  simp only [commonRowCLM,jetFamilyCLM_apply,flatJetCLM_apply]

/-- A common Hessian row is genuinely uncorrelated with the full two-value
score observation at either point, even though it couples to gradients. -/
theorem common_row_score_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0) :
    (commonRowCLM c x e v).comp (normalizedScore c y).adjoint=0 := by
  ext w i
  change commonRowCLM c x e v ((normalizedScore c y).adjoint w) i=0
  rw [commonRowCLM_apply,← scalarCross_right_dual,normalizedScore_dual]
  simp only [scalarCross_add_right,scalarCross_smul_right,scalarCross_flatJet]
  rw [hessian_value_covariance hN c hc,hessian_radial_covariance hN c hc hdeg]
  simp only [htany,mul_zero,zero_mul,add_zero]

/-- Exact common-row/gradient coupling after common orthogonality removes
all third-profile terms. Only the corresponding common gradient remains. -/
theorem common_row_gradient_coupling {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) (w : EuclideanSpace ℝ (Fin k)) (i : Fin m) :
    commonRowCLM c x e v ((gradientCLM c y f).adjoint w) i=
      secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ (e i) (frameSum f w)*inner ℝ v y := by
  rw [commonRowCLM_apply,← scalarCross_right_dual,gradientCLM_dual,scalarCross_flatJet,
    hessian_gradient_covariance hN c hc hdeg]
  simp only [htany,mul_zero,zero_mul,add_zero,zero_add]
  ring

/-- The row is also genuinely uncorrelated with the opposite in-plane
scalar gradient; the chosen plane direction is literal and normalized. -/
theorem common_row_planeGradient_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0) :
    (commonRowCLM c x e v).comp (flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro t
  apply PiLp.ext
  intro i
  change commonRowCLM c x e v ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint t) i=0
  rw [commonRowCLM_apply]
  have hcross : scalarCross (flatJetCLM c 2 x ![e i,v])
      (flatJetCLM c 1 y (fun _=>planeDirection y x))=0 := by
    rw [scalarCross_flatJet,hessian_gradient_covariance hN c hc hdeg]
    simp only [htany,planeDirection_common_inner y x (e i) (htany i) (htanx i),mul_zero,zero_mul,add_zero]
  have hlin : (flatJetCLM c 2 x ![e i,v]).comp
      (flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint=0 := by
    apply ContinuousLinearMap.ext
    intro s
    have h1 : (flatJetCLM c 2 x ![e i,v]) ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint 1)=0 := hcross
    change (flatJetCLM c 2 x ![e i,v]) ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint s)=0
    calc
      _=s*(flatJetCLM c 2 x ![e i,v]) ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint 1) := by
        change (flatJetCLM c 2 x ![e i,v]) ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint s)=
          s • (flatJetCLM c 2 x ![e i,v]) ((flatJetCLM c 1 y (fun _=>planeDirection y x)).adjoint 1)
        rw [← map_smul,← map_smul,smul_eq_mul,mul_one]
      _=0 := by rw [h1,mul_zero]
  exact congrArg (fun A:ℝ→L[ℝ]ℝ=>A t) hlin

end
end SlowEquilibration.SphericalCommonHessianRegression
