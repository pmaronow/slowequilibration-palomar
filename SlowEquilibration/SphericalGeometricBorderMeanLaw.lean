-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalBorderedIntrinsicDeterminant
public import SlowEquilibration.SinglePointBulkBorderLaw
public import SlowEquilibration.PhysicalBorderSchurExpectation

/-! Literal geometric full border normalization equals the true adjacent
GOE mean under every original own-point tensor posterior target. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression SphericalCommonHessianRegression NormalizedPairObservations
open PhysicalCommonBorderMoments GOEPhysicalPotential GOERawMoments
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Actual geometric full bordered determinant is the shifted full Hessian
in its complete tangent basis, at every original disorder coefficient. -/
theorem geometric_fullBorder_eq_shifted_absoluteDet {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+3) P) (x y : Vector (n+3))
    (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ)) (hr : |overlap x y| < 1) (k : ℝ) :
    fullBorder (n:=n) (hessianMatrix (k:=n+1) c x (commonFrame (by omega) x y hx hy hr)) k
      (actualObservation (cornerCLM c x (planeDirection x y)))
      (actualObservation (commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y))) J =
      matrixAbsoluteDet (n+1) k (hessianMatrix c x (borderedFrame x y hx hy hr) J) := by
  symm
  unfold matrixAbsoluteDet
  rw [← Matrix.det_reindex_self (borderIndexEquiv (n+1)).symm
    (k • (1:Matrix (Fin (n+2)) (Fin (n+2)) ℝ)-hessianMatrix c x (borderedFrame x y hx hy hr) J),
    full_shifted_hessian_eq_border]
  change |(GOEBorderedDeterminant.border
    (k-jet c 2 x ![planeDirection x y,planeDirection x y] J)
    (-fun i=>jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
    (-fun i=>jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
    (k • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-hessianMatrix (k:=n+1) c x (commonFrame (by omega) x y hx hy hr) J)).det|=_
  rw [border_neg_row_det]
  have hRow : (actualObservation (commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y)) J).ofLp=
      (fun i=>jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J) := by
    funext i
    change commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y) (euclideanDisorder J) i=_
    rw [commonRowCLM_apply,flatJetCLM_apply,unpack_euclideanDisorder]
  unfold fullBorder
  rw [hRow,actual_corner_eq_jet]

/-- The ordinary full-border expectation equals μ_{N−1,N} exactly; no
comparison, determinant law, or ordinary expectation is supplied as a premise. -/
theorem geometric_fullBorder_mixed_integral_eq_adjacentMean {n P ℓ : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hr : |overlap x y| < 1) (f : Fin ℓ → Vector (n+3))
    (w : MixedObservationSpace ℓ) (k : ℝ) :
    (∫ J,fullBorder (n:=n) (hessianMatrix (k:=n+1) c x (commonFrame (by omega) x y hx hy hr)) k
      (actualObservation (cornerCLM c x (planeDirection x y)))
      (actualObservation (commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y))) J
      ∂coefficientKernel (singleMixedObservation c x f) w) =
      physicalMean (n+1) (n+3) (secondCovariance c 1) k := by
  have hLaw:=single_common_matrix_mixed_hasLaw (by omega : 0 < n+3) c hc hdeg x hx
    (borderedFrame x y hx hy hr) (borderedFrame_orthonormal x y hx hy hr)
    (borderedFrame_tangent x y hx hy hr) f w
  have hEq:=hLaw.integral_comp (matrixAbsoluteDet_measurable (n+1) k).aestronglyMeasurable
  simp only [Function.comp_def] at hEq
  simp only [← geometric_fullBorder_eq_shifted_absoluteDet (n:=n) c _ x y hx hy hr k] at hEq
  exact hEq

/-- Proper value-only conditioning gives the same exact adjacent mean. -/
theorem geometric_fullBorder_value_integral_eq_adjacentMean {n P ℓ : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector (n+3)) (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ))
    (hr : |overlap x y| < 1) (f : Fin ℓ → Vector (n+3))
    (w : ValueObservationSpace ℓ) (k : ℝ) :
    (∫ J,fullBorder (n:=n) (hessianMatrix (k:=n+1) c x (commonFrame (by omega) x y hx hy hr)) k
      (actualObservation (cornerCLM c x (planeDirection x y)))
      (actualObservation (commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y))) J
      ∂coefficientKernel (singleValueObservation c x f) w) =
      physicalMean (n+1) (n+3) (secondCovariance c 1) k := by
  have hLaw:=single_common_matrix_value_hasLaw (by omega : 0 < n+3) c hc hdeg x hx
    (borderedFrame x y hx hy hr) (borderedFrame_orthonormal x y hx hy hr)
    (borderedFrame_tangent x y hx hy hr) f w
  have hEq:=hLaw.integral_comp (matrixAbsoluteDet_measurable (n+1) k).aestronglyMeasurable
  simp only [Function.comp_def] at hEq
  simp only [← geometric_fullBorder_eq_shifted_absoluteDet (n:=n) c _ x y hx hy hr k] at hEq
  exact hEq

end
end SlowEquilibration.SphericalPairCommonFrame
