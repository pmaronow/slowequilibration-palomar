-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OrderedTensorSlotPermutation
public import SphericalAging.HamiltonianBallBounds

/-! Genuine exponentially probable uniform physical bounds for every
fixed ordered trace bank, transferred from its proved original iid law. -/

@[expose] public section
namespace SlowEquilibration.OrderedTensorTraceGaussianBank
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalAging.FiniteModel SphericalAging.GaussianLandscape
open SphericalAging.LandscapeDerivatives
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def traceLandscapeNorm (N q j : ℕ) (σ : Equiv.Perm (Fin (q+j+j)))
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) : ℝ :=
  landscapeNorm N q (rawOrderedTensorTrace N q j (permutedTensor σ J))

/-- True exponentially small exceptional probability for an actual original
trace tensor. Constants depend only on its fixed free degree. -/
theorem traceLandscapeNorm_failure_probability {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q)
    (j : ℕ) (σ : Equiv.Perm (Fin (q+j+j))) :
    (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
      {J | landscapeThreshold q+4 < traceLandscapeNorm N q j σ J} ≤
      Real.exp (-(N : ℝ)) := by
  have hSet : MeasurableSet {K : SphericalAging.FiniteModel.Disorder N q |
      landscapeThreshold q+4 < landscapeNorm N q K} :=
    (isOpen_lt continuous_const (landscapeNorm_continuous N q)).measurableSet
  have h := (actual_permutedTensorTrace_hasLaw (by omega : 0 < N) q j σ).measureReal_eq hSet
  change (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
    {J | landscapeThreshold q+4 < traceLandscapeNorm N q j σ J}=_ at h
  rw [h]
  exact landscape_exponential_dimension_bound hN hq

/-- On the actual trace regularity event, the literal physical traced
Hamiltonian has the exact uniform manuscript scale throughout its ball. -/
theorem permutedTracedHamiltonian_abs_le_of_traceRegular {N q : ℕ} (hN : 0 < N)
    (hq : 1 ≤ q) (j : ℕ) (σ : Equiv.Perm (Fin (q+j+j)))
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (C : ℝ)
    (hJ : traceLandscapeNorm N q j σ J ≤ C) (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    |permutedTracedHamiltonian N q j σ J x| ≤ C*(N : ℝ)^(1-(j : ℝ)/2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnorm : normalization N q≠0 := (Real.rpow_pos_of_pos hNr _).ne'
  have hs : 0 ≤ normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)/normalization N q := by
    apply div_nonneg
    · exact mul_nonneg (Real.rpow_nonneg hNr.le _) (Real.sqrt_nonneg _)
    · exact Real.rpow_nonneg hNr.le _
  have hH := (SphericalAging.HamiltonianBallBounds.Hamiltonian_ball_bound hN hq
    (rawOrderedTensorTrace N q j (permutedTensor σ J)) hx).trans hJ
  have hH' : |Hamiltonian N q (rawOrderedTensorTrace N q j (permutedTensor σ J)) x| ≤ C*(N : ℝ) :=
    (div_le_iff₀ hNr).mp hH
  have hqn : normalization N q*(Real.sqrt N)^q*Real.sqrt N=(N : ℝ) := by
    simpa only [Nat.sub_zero,Nat.cast_zero,zero_div,sub_zero,Real.rpow_one] using
      PureTensorJetBounds.physical_normalization_identity hN hq (show 0 ≤ q by omega)
  have hscale : (normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)/normalization N q)*(N : ℝ)=
      (N : ℝ)^(1-(j : ℝ)/2) := by
    calc
      _=normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*Real.sqrt N := by
        conv_lhs => arg 2;rw [←hqn]
        field_simp [hnorm]
      _=_ := trace_physical_normalization hN hq j
  unfold permutedTracedHamiltonian
  rw [tracedHamiltonian_eq_actual_bank hN q j,abs_mul,abs_of_nonneg hs]
  apply (mul_le_mul_of_nonneg_left hH' hs).trans_eq
  rw [mul_left_comm,hscale]

end
end SlowEquilibration.OrderedTensorTraceGaussianBank
