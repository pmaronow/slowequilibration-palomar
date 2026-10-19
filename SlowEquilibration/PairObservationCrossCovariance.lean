-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.SphericalTwoPointCovariance
public import SlowEquilibration.ScalarCoefficientCovariance

/-! Literal bilinear cross Gram forms of the normalized actual two-point
observations. No dimension-sized matrix norm estimate is substituted. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma value_value_two_point {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) :
    cov[jet c 0 x (fun i => Fin.elim0 i),jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      (N:ℝ)*covariancePolynomial c (overlap x y) := by
  have hjet (z : Vector N) : jet c 0 z (fun i => Fin.elim0 i)=(fun J => field c J z) := by
    funext J
    simp only [jet,iteratedFDeriv_zero_apply]
  rw [hjet x,hjet y]
  exact field_covariance hN c hc x y

/-- Exact cross covariance of actual Hilbert dual mixed observations. -/
theorem mixed_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (e f : Fin m → Vector N)
    (u v : MixedObservationSpace m) :
    let r:=overlap x y
    let U:=frameSum e u.snd
    let V:=frameSum f v.snd
    inner ℝ u (singleMixedObservation c x e ((singleMixedObservation c y f).adjoint v))=
      u.fst 0*v.fst 0*covariancePolynomial c r+
      u.fst 0*v.fst 1*(r*firstCovariance c r)+
      u.fst 1*v.fst 0*(r*firstCovariance c r)+
      u.fst 1*v.fst 1*(r*firstCovariance c r+r^2*secondCovariance c r)+
      (u.fst 0/Real.sqrt (N:ℝ))*firstCovariance c r*inner ℝ x V+
      (u.fst 1/Real.sqrt (N:ℝ))*(firstCovariance c r+r*secondCovariance c r)*inner ℝ x V+
      (v.fst 0/Real.sqrt (N:ℝ))*firstCovariance c r*inner ℝ U y+
      (v.fst 1/Real.sqrt (N:ℝ))*(firstCovariance c r+r*secondCovariance c r)*inner ℝ U y+
      firstCovariance c r*inner ℝ U V+
      secondCovariance c r/(N:ℝ)*inner ℝ U y*inner ℝ x V := by
  dsimp only
  rw [← scalarCross_dual,singleMixedObservation_dual,singleMixedObservation_dual]
  simp only [scalarCross_add_left,scalarCross_add_right,scalarCross_smul_left,
    scalarCross_smul_right,scalarCross_flatJet]
  have h00:=value_value_two_point hN c hc x y
  have h01:=value_radial_two_point_covariance hN c hc x y
  have h10 : cov[jet c 1 x (fun _ => x),jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      (N:ℝ)*overlap x y*firstCovariance c (overlap x y) := by
    rw [covariance_comm,value_radial_two_point_covariance hN c hc y x,overlap_comm]
  have h11:=radial_radial_two_point_covariance hN c hc x y
  have h02 : cov[jet c 0 x (fun i => Fin.elim0 i),
      jet c 1 y (fun _ => frameSum f v.snd);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ x (frameSum f v.snd) := by
    rw [covariance_comm,gradient_value_covariance hN c hc y x,overlap_comm,real_inner_comm]
  have h12 : cov[jet c 1 x (fun _ => x),
      jet c 1 y (fun _ => frameSum f v.snd);disorderLaw N P]=
      (firstCovariance c (overlap x y)+overlap x y*secondCovariance c (overlap x y))*
        inner ℝ x (frameSum f v.snd) := by
    rw [covariance_comm,gradient_radial_covariance hN c hc y x,overlap_comm,real_inner_comm]
  rw [h00,h01,h10,h11,h02,h12,
    gradient_value_covariance hN c hc x y,gradient_radial_covariance hN c hc x y,
    gradient_gradient_covariance hN c hc x y]
  have hs : Real.sqrt (N:ℝ)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Proper value-only cross covariance; no redundant radial observation. -/
theorem value_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (e f : Fin m → Vector N)
    (u v : ValueObservationSpace m) :
    let r:=overlap x y
    let U:=frameSum e u.snd
    let V:=frameSum f v.snd
    inner ℝ u (singleValueObservation c x e ((singleValueObservation c y f).adjoint v))=
      u.fst*v.fst*covariancePolynomial c r+
      (u.fst/Real.sqrt (N:ℝ))*firstCovariance c r*inner ℝ x V+
      (v.fst/Real.sqrt (N:ℝ))*firstCovariance c r*inner ℝ U y+
      firstCovariance c r*inner ℝ U V+
      secondCovariance c r/(N:ℝ)*inner ℝ U y*inner ℝ x V := by
  dsimp only
  rw [← scalarCross_dual,singleValueObservation_dual,singleValueObservation_dual]
  simp only [scalarCross_add_left,scalarCross_add_right,scalarCross_smul_left,
    scalarCross_smul_right,scalarCross_flatJet]
  have h02 : cov[jet c 0 x (fun i => Fin.elim0 i),
      jet c 1 y (fun _ => frameSum f v.snd);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ x (frameSum f v.snd) := by
    rw [covariance_comm,gradient_value_covariance hN c hc y x,overlap_comm,real_inner_comm]
  rw [value_value_two_point hN c hc x y,h02,gradient_value_covariance hN c hc x y,
    gradient_gradient_covariance hN c hc x y]
  have hs : Real.sqrt (N:ℝ)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end
end SlowEquilibration.PairObservationCrossCovariance
