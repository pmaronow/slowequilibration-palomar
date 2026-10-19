-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedObservationBlocks
public import SlowEquilibration.PairObservationCrossCovariance

/-! Exact score/score, score/gradient and gradient/gradient cross blocks
of the actual normalized two-point Gaussian observations. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open NormalizedPairObservations SphericalTwoPointCovariance ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

theorem score_cross_inner {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (u v : EuclideanSpace ℝ (Fin 2)) :
    let r:=overlap x y
    inner ℝ u (normalizedScore c x ((normalizedScore c y).adjoint v))=
      u 0*v 0*covariancePolynomial c r+u 0*v 1*(r*firstCovariance c r)+
      u 1*v 0*(r*firstCovariance c r)+u 1*v 1*(r*firstCovariance c r+r^2*secondCovariance c r) := by
  dsimp only
  rw [← scalarCross_dual,normalizedScore_dual,normalizedScore_dual]
  simp only [scalarCross_add_left,scalarCross_add_right,scalarCross_smul_left,
    scalarCross_smul_right,scalarCross_flatJet]
  have h10 : cov[jet c 1 x (fun _ => x),jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      (N:ℝ)*overlap x y*firstCovariance c (overlap x y) := by
    rw [covariance_comm,value_radial_two_point_covariance hN c hc y x,overlap_comm]
  rw [value_value_two_point hN c hc x y,value_radial_two_point_covariance hN c hc x y,
    h10,radial_radial_two_point_covariance hN c hc x y]
  have hs : Real.sqrt (N:ℝ)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem score_gradient_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (f : Fin m → Vector N)
    (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin m)) :
    let r:=overlap x y
    let V:=frameSum f v
    inner ℝ u (normalizedScore c x ((gradientCLM c y f).adjoint v))=
      u 0*firstCovariance c r*(inner ℝ x V/Real.sqrt (N:ℝ))+
      u 1*(firstCovariance c r+r*secondCovariance c r)*(inner ℝ x V/Real.sqrt (N:ℝ)) := by
  dsimp only
  rw [← scalarCross_dual,normalizedScore_dual,gradientCLM_dual]
  simp only [scalarCross_add_left,scalarCross_smul_left,scalarCross_flatJet]
  have h02 : cov[jet c 0 x (fun i => Fin.elim0 i),jet c 1 y (fun _ => frameSum f v);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ x (frameSum f v) := by
    rw [covariance_comm,gradient_value_covariance hN c hc y x,overlap_comm,real_inner_comm]
  have h12 : cov[jet c 1 x (fun _ => x),jet c 1 y (fun _ => frameSum f v);disorderLaw N P]=
      (firstCovariance c (overlap x y)+overlap x y*secondCovariance c (overlap x y))*inner ℝ x (frameSum f v) := by
    rw [covariance_comm,gradient_radial_covariance hN c hc y x,overlap_comm,real_inner_comm]
  rw [h02,h12]
  ring

theorem gradient_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (e f : Fin m → Vector N)
    (u v : EuclideanSpace ℝ (Fin m)) :
    let r:=overlap x y
    let U:=frameSum e u
    let V:=frameSum f v
    inner ℝ u (gradientCLM c x e ((gradientCLM c y f).adjoint v))=
      firstCovariance c r*inner ℝ U V+
      secondCovariance c r*(inner ℝ U y/Real.sqrt (N:ℝ))*(inner ℝ x V/Real.sqrt (N:ℝ)) := by
  dsimp only
  rw [← scalarCross_dual,gradientCLM_dual,gradientCLM_dual,scalarCross_flatJet,
    gradient_gradient_covariance hN c hc x y]
  have hs : Real.sqrt (N:ℝ)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end
end SlowEquilibration.PairObservationCrossCovariance
