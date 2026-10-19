-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTwoPointCovariance
public import SlowEquilibration.IntrinsicHessianLaw

@[expose] public section

/-! Exact coefficient-space covariance of the actual transverse Taylor
remainder, and orthogonality to every first-order observation at its center. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.SphericalTwoPointCovariance
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def valueObservation {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  flatJetCLM c 0 x (fun i => Fin.elim0 i)

def directionObservation {N P : ℕ} (c : Degree P → ℝ) (x v : Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  flatJetCLM c 1 x (fun _ => v)

def taylorRemainderCLM {N P : ℕ} (c : Degree P → ℝ) (m z : Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  valueObservation c (m+z)-valueObservation c m-directionObservation c m z

@[simp] theorem valueObservation_actual {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (J : Disorder N P) : valueObservation c x (euclideanDisorder J)=field c J x := by
  simp only [valueObservation,flatJetCLM_apply,unpack_euclideanDisorder,jet,iteratedFDeriv_zero_apply]

@[simp] theorem directionObservation_actual {N P : ℕ} (c : Degree P → ℝ) (x v : Vector N)
    (J : Disorder N P) : directionObservation c x v (euclideanDisorder J)=fderiv ℝ (field c J) x v := by
  simp only [directionObservation,flatJetCLM_apply,unpack_euclideanDisorder,jet,iteratedFDeriv_one_apply]

@[simp] theorem taylorRemainderCLM_actual {N P : ℕ} (c : Degree P → ℝ) (m z : Vector N)
    (J : Disorder N P) : taylorRemainderCLM c m z (euclideanDisorder J)=
      field c J (m+z)-field c J m-fderiv ℝ (field c J) m z := by
  simp only [taylorRemainderCLM,sub_apply,valueObservation_actual,directionObservation_actual]

theorem scalar_observation_covariance {N P : ℕ}
    (f g : EuclideanDisorder N P →L[ℝ] ℝ) :
    cov[fun J : Disorder N P => f (euclideanDisorder J),fun J => g (euclideanDisorder J);disorderLaw N P]=
      f (g.adjoint 1) := by
  simpa using actual_scalar_cross_covariance f g 1

theorem scalar_coupling_comm {N P : ℕ} (f g : EuclideanDisorder N P →L[ℝ] ℝ) :
    f (g.adjoint 1)=g (f.adjoint 1) := by
  rw [← scalar_observation_covariance, ← scalar_observation_covariance, covariance_comm]

theorem value_value_coupling {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (x y : Vector N) : valueObservation c x ((valueObservation c y).adjoint 1)=
      (N : ℝ)*covariancePolynomial c (overlap x y) := by
  rw [← scalar_observation_covariance]
  simpa only [valueObservation_actual] using field_covariance hN c hc x y

theorem direction_value_coupling {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (x y v : Vector N) : directionObservation c x v ((valueObservation c y).adjoint 1)=
      firstCovariance c (overlap x y)*inner ℝ v y := by
  rw [← scalar_observation_covariance]
  simpa only [directionObservation,valueObservation,flatJetCLM_apply,unpack_euclideanDisorder] using
    gradient_value_covariance hN c hc x y v

theorem direction_direction_coupling {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (x y u v : Vector N) : directionObservation c x u ((directionObservation c y v).adjoint 1)=
      firstCovariance c (overlap x y)*inner ℝ u v+
        secondCovariance c (overlap x y)/(N : ℝ)*inner ℝ u y*inner ℝ x v := by
  rw [← scalar_observation_covariance]
  simpa only [directionObservation,flatJetCLM_apply,unpack_euclideanDisorder] using
    gradient_gradient_covariance hN c hc x y u v

theorem overlap_center_transverse {N : ℕ} (m z : Vector N) (hz : inner ℝ z m=0) :
    overlap (m+z) m=overlap m m ∧ overlap m (m+z)=overlap m m := by
  have hz' : inner ℝ m z=0 := by rw [real_inner_comm]; exact hz
  simp [overlap,inner_add_left,inner_add_right,hz,hz']

theorem taylorRemainder_value_orthogonal {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (m z : Vector N) (hz : inner ℝ z m=0) :
    taylorRemainderCLM c m z ((valueObservation c m).adjoint 1)=0 := by
  simp only [taylorRemainderCLM,sub_apply]
  rw [value_value_coupling hN c hc,value_value_coupling hN c hc,direction_value_coupling hN c hc,
    (overlap_center_transverse m z hz).1,hz,mul_zero,sub_self,sub_zero]

theorem taylorRemainder_direction_orthogonal {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (m z v : Vector N) (hz : inner ℝ z m=0) :
    taylorRemainderCLM c m z ((directionObservation c m v).adjoint 1)=0 := by
  simp only [taylorRemainderCLM,sub_apply]
  rw [scalar_coupling_comm (valueObservation c (m+z)),scalar_coupling_comm (valueObservation c m),
    direction_value_coupling hN c hc,direction_value_coupling hN c hc,direction_direction_coupling hN c hc,
    (overlap_center_transverse m z hz).2,hz,mul_zero,zero_mul,add_zero,inner_add_right]
  rw [real_inner_comm v z]
  ring

/-- Exact covariance of the two actual transverse Taylor remainders. -/
theorem taylorRemainder_coupling {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (m z t : Vector N) (hz : inner ℝ z m=0) (ht : inner ℝ t m=0) :
    taylorRemainderCLM c m z ((taylorRemainderCLM c m t).adjoint 1)=
      (N : ℝ)*(covariancePolynomial c (overlap m m+overlap z t)-covariancePolynomial c (overlap m m))-
        firstCovariance c (overlap m m)*inner ℝ z t := by
  have hmz : inner ℝ m z=0 := by rw [real_inner_comm]; exact hz
  have hmt : inner ℝ m t=0 := by rw [real_inner_comm]; exact ht
  have ho : overlap (m+z) (m+t)=overlap m m+overlap z t := by
    simp only [overlap,inner_add_left,inner_add_right,hz,hmt,zero_add,add_zero,add_div]
  have hright : taylorRemainderCLM c m z ((taylorRemainderCLM c m t).adjoint 1)=
      taylorRemainderCLM c m z ((valueObservation c (m+t)).adjoint 1) := by
    rw [scalar_coupling_comm (taylorRemainderCLM c m z)]
    change (valueObservation c (m+t)-valueObservation c m-directionObservation c m t)
      ((taylorRemainderCLM c m z).adjoint 1)=_
    simp only [sub_apply]
    rw [scalar_coupling_comm (valueObservation c (m+t)), scalar_coupling_comm (valueObservation c m),
      scalar_coupling_comm (directionObservation c m t),
      taylorRemainder_value_orthogonal hN c hc m z hz,
      taylorRemainder_direction_orthogonal hN c hc m z t hz,sub_zero,sub_zero]
  rw [hright]
  simp only [taylorRemainderCLM,sub_apply]
  rw [value_value_coupling hN c hc,value_value_coupling hN c hc,direction_value_coupling hN c hc,
    ho,(overlap_center_transverse m t ht).2,inner_add_right,hz,zero_add]
  ring

end
end SlowEquilibration.SphericalTaylorRemainder
