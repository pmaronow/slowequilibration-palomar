-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetResidualOrthogonality
public import SlowEquilibration.SphericalCommonHessianCovariance

@[expose] public section

/-! The part of the original latitude field remaining after the degree-two
Taylor bank is orthogonal to the genuine scaled-center tangential Hessian.
The proof compares the actual second/zero and second/second tensor covariances
degree by degree; it does not posit Gaussian-bank independence. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTwoPointCovariance
open SphericalAging.FiniteModel (Hamiltonian)
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem pure_center_hessian_latitude_covariance_eq_quadratic
    {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u v w ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hv : inner ℝ v u=0) (hw : inner ℝ w u=0)
    (hω : inner ℝ ω u=0) :
    cov[fun J : PureDisorder N p =>
        iteratedFDeriv ℝ 2 (Hamiltonian N p J) u ![v,w],
      fun J : PureDisorder N p =>
        iteratedFDeriv ℝ 0 (Hamiltonian N p J)
          (originalLatitudePoint a u ω) (fun i => Fin.elim0 i);
      PureLaw N p] =
      ((1-a^2)/2) *
        cov[fun J : PureDisorder N p =>
            iteratedFDeriv ℝ 2 (Hamiltonian N p J) u ![v,w],
          fun J : PureDisorder N p =>
            iteratedFDeriv ℝ 2 (Hamiltonian N p J) (a • u) ![ω,ω];
          PureLaw N p] := by
  let σ := originalLatitudePoint a u ω
  have hNreal : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have huω : inner ℝ u ω=0 := by rw [real_inner_comm]; exact hω
  have hvσ : inner ℝ v σ = Real.sqrt (1-a^2)*inner ℝ v ω := by
    simp [σ,originalLatitudePoint,inner_add_right,inner_smul_right,hv]
  have hwσ : inner ℝ w σ = Real.sqrt (1-a^2)*inner ℝ w ω := by
    simp [σ,originalLatitudePoint,inner_add_right,inner_smul_right,hw]
  have hover : overlap u σ = a := by
    unfold overlap σ originalLatitudePoint
    simp only [inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hu,huω,mul_zero,add_zero]
    field_simp
  have hover2 : overlap u (a • u) = a := by
    unfold overlap
    rw [inner_smul_right,real_inner_self_eq_norm_sq,hu]
    field_simp
  have hvat : inner ℝ v (a • u)=0 := by rw [inner_smul_right,hv,mul_zero]
  have hwat : inner ℝ w (a • u)=0 := by rw [inner_smul_right,hw,mul_zero]
  rw [pure_hessian_value_covariance hN hp,
    pure_common_hessian_covariance hN hp u (a • u) v w ω ω hvat hwat,
    hover,hover2,hvσ,hwσ]
  have hs : (Real.sqrt (1-a^2))^2=1-a^2 := Real.sq_sqrt ha
  calc
    (p:ℝ)*((p:ℝ)-1)*a^(p-2)/(N:ℝ)*
        (Real.sqrt (1-a^2)*inner ℝ v ω)*
        (Real.sqrt (1-a^2)*inner ℝ w ω) =
      (Real.sqrt (1-a^2))^2 *
        ((p:ℝ)*((p:ℝ)-1)*a^(p-2)/(N:ℝ)*
          inner ℝ v ω*inner ℝ w ω) := by ring
    _ = (1-a^2)*
        ((p:ℝ)*((p:ℝ)-1)*a^(p-2)/(N:ℝ)*
          inner ℝ v ω*inner ℝ w ω) := by rw [hs]
    _ = _ := by ring

/-- The scaled-center Hessian has exactly the same covariance with the
full latitude field and its genuine quadratic Taylor bank. -/
theorem scaledCenterHessian_originalLatitudeField_covariance_eq_quadratic
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (Q a : ℝ) (ha : 0 ≤ 1-a^2) (u v w ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hv : inner ℝ v u=0) (hw : inner ℝ w u=0)
    (hω : inner ℝ ω u=0) :
    cov[jet (centerCoefficients (mixtureCoefficients μ) Q) 2 u ![v,w],
      fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω);
      disorderLaw N μ.maxDegree] =
    cov[jet (centerCoefficients (mixtureCoefficients μ) Q) 2 u ![v,w],
      quadraticLatitudeJet μ a u ω;
      disorderLaw N μ.maxDegree] := by
  let c := mixtureCoefficients μ
  let cQ := centerCoefficients c Q
  let σ := originalLatitudePoint a u ω
  have hfield : (fun J : Disorder N μ.maxDegree => field c J σ) =
      jet c 0 σ (fun i => Fin.elim0 i) := by
    funext J
    simp only [jet,iteratedFDeriv_zero_apply]
  rw [hfield,jet_cross_covariance]
  unfold quadraticLatitudeJet
  rw [covariance_const_mul_right,jet_cross_covariance,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pure_center_hessian_latitude_covariance_eq_quadratic
    hN p.property a ha u v w ω hu hv hw hω]
  ring

/-- Consequently the nonquadratic part of the genuine original latitude
field is orthogonal to every tangential entry of the actual physical
scaled-center Hessian. -/
theorem scaledCenterHessian_residualField_covariance_zero
    {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (Q a : ℝ) (ha : 0 ≤ 1-a^2) (u v w ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ))
    (hv : inner ℝ v u=0) (hw : inner ℝ w u=0)
    (hω : inner ℝ ω u=0) :
    cov[jet (centerCoefficients (mixtureCoefficients μ) Q) 2 u ![v,w],
      fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω) - quadraticLatitudeJet μ a u ω J;
      disorderLaw N μ.maxDegree] = 0 := by
  have hH : MemLp (jet (centerCoefficients (mixtureCoefficients μ) Q)
      2 u ![v,w]) 2 (disorderLaw N μ.maxDegree) := jet_memLp _ _ _ _
  have hfield : MemLp (fun J : Disorder N μ.maxDegree =>
      field (mixtureCoefficients μ) J (originalLatitudePoint a u ω)) 2
      (disorderLaw N μ.maxDegree) := by
    convert jet_memLp (mixtureCoefficients μ) 0
      (originalLatitudePoint a u ω) (fun i => Fin.elim0 i) using 1
    funext J
    simp only [jet,iteratedFDeriv_zero_apply]
  have hjet : MemLp (quadraticLatitudeJet μ a u ω) 2
      (disorderLaw N μ.maxDegree) :=
    (jet_memLp (mixtureCoefficients μ) 2 (a • u) ![ω,ω]).const_mul _
  rw [covariance_fun_sub_right hH hfield hjet,
    scaledCenterHessian_originalLatitudeField_covariance_eq_quadratic
      hN μ Q a ha u v w ω hu hv hw hω]
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
