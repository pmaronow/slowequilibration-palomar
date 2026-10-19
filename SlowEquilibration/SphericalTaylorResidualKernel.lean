-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorRemainderConditioning
public import SlowEquilibration.FiniteMixtureTaylorResidual

@[expose] public section

/-! The literal centered-tensor transverse field has exactly the genuine
finite-mixture Taylor-residual covariance, including the physical dimension
and transverse radius normalization. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem covariancePolynomial_center {P : ℕ} (c : Degree P → ℝ) (Q t : ℝ) :
    covariancePolynomial (centerCoefficients c Q) t=covariancePolynomial c (Q*t) := by
  unfold covariancePolynomial centerCoefficients
  simp only [mul_pow]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem center_taylorRemainder_coupling {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (m z t : Vector N)
    (hm : ‖m‖^2=(N : ℝ)) (hz : inner ℝ z m=0) (ht : inner ℝ t m=0)
    (r : ℝ) (hzt : inner ℝ z t=(N : ℝ)*((1-q)/q)*r) :
    let c := centerCoefficients (mixtureCoefficients μ) q
    taylorRemainderCLM c m z ((taylorRemainderCLM c m t).adjoint 1)=
      (N : ℝ)*(μ.taylorResidual hq.1 (sub_pos.mpr hq.2)).xi r := by
  dsimp only
  rw [taylorRemainder_coupling hN _ (centerCoefficients_nonnegative _
    (mixtureCoefficients_nonnegative μ) hq.1.le) m z t hz ht,
    overlap_self hN m hm,covariancePolynomial_center,covariancePolynomial_center_one,
    covariancePolynomial_mixture,covariancePolynomial_mixture,
    firstCovariance_center,firstCovariance_mixture,FiniteMixture.taylorResidual_xi]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hR : overlap z t=((1-q)/q)*r := by unfold overlap; rw [hzt]; field_simp
  rw [hR]
  have harg : q*(1+(1-q)/q*r)=q+(1-q)*r := by field_simp [hq.1.ne']
  rw [harg,hzt]
  field_simp [hq.1.ne']

def transverseOffset {N d : ℕ} (e : Vector d →ₗᵢ[ℝ] Vector N) (q : ℝ) (y : Vector d) : Vector N :=
  Real.sqrt ((N : ℝ)*(1-q)/(q*(d : ℝ))) • e y

theorem transverseOffset_tangent {N d : ℕ} (m : Vector N) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (he : ∀ y,inner ℝ (e y) m=0) (q : ℝ) (y : Vector d) :
    inner ℝ (transverseOffset e q y) m=0 := by
  rw [transverseOffset,inner_smul_left,he,mul_zero]

theorem transverseOffset_inner {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (e : Vector d →ₗᵢ[ℝ] Vector N) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (y z : Vector d) : inner ℝ (transverseOffset e q y) (transverseOffset e q z)=
      (N : ℝ)*((1-q)/q)*overlap y z := by
  have hq0 := hq.1
  have hq1 := sub_pos.mpr hq.2
  rw [transverseOffset,transverseOffset,real_inner_smul_left,real_inner_smul_right,e.inner_map_map,
    ← mul_assoc,← pow_two,Real.sq_sqrt (by positivity)]
  unfold overlap
  ring

/-- Actual scalar covariance at every pair of transverse parameters. -/
theorem transverse_taylorRemainder_kernel {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (μ : FiniteMixture) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (m : Vector N) (hm : ‖m‖^2=(N : ℝ)) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (he : ∀ y,inner ℝ (e y) m=0) (y z : Vector d) :
    let c := centerCoefficients (mixtureCoefficients μ) q
    taylorRemainderCLM c m (transverseOffset e q y)
      ((taylorRemainderCLM c m (transverseOffset e q z)).adjoint 1)=
        (N : ℝ)*(μ.taylorResidual hq.1 (sub_pos.mpr hq.2)).xi (overlap y z) := by
  exact center_taylorRemainder_coupling hN μ hq m _ _ hm
    (transverseOffset_tangent m e he q y) (transverseOffset_tangent m e he q z)
    (overlap y z) (transverseOffset_inner hN hd e hq y z)

end
end SlowEquilibration.SphericalTaylorRemainder
