-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalHSTruncation
public import SlowEquilibration.SphericalMomentLower

@[expose] public section

/-!
# Physical pressure lower bound from the concrete HS typicality event

All first and second moments used here are calculated for the actual HS
truncated partition. The sole probabilistic input remaining is the planted
mass of its explicitly constructed typicality event. In particular there is
no unspecified candidate random variable or assumed second-moment estimate.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The concrete HS event with a fixed extensive gap has a normalized
second-moment ratio bounded independently of any typicality assumption. -/
theorem expected_hsTruncatedPartition_sq_gap_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) :
    (∫ J, (truncatedPartition c β
      (hsTruncation c β δ (annealedExponent N c β-(N : ℝ)*η)) J)^2 ∂disorderLaw N P) ≤
      2*Real.exp (2*annealedExponent N c β+(N : ℝ)*β^2*covariancePolynomial c 1*δ^2) := by
  have h := expected_hsTruncatedPartition_sq_le hN c hc β
    (annealedExponent N c β-(N : ℝ)*η) hδ hδ1
  have hc1 : 0 ≤ covariancePolynomial c 1 := by
    unfold covariancePolynomial
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (hc p) (by positivity))
  have hfar : annealedExponent N c β-(N : ℝ)*η+(N : ℝ)*β^2*covariancePolynomial c 1/2 ≤
      2*annealedExponent N c β+(N : ℝ)*β^2*covariancePolynomial c 1*δ^2 := by
    unfold annealedExponent
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hη,
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β)) hc1) (sq_nonneg δ)]
  have he : (N : ℝ)*β^2*covariancePolynomial c 1*(1+δ^2) =
      2*annealedExponent N c β+(N : ℝ)*β^2*covariancePolynomial c 1*δ^2 := by
    unfold annealedExponent
    ring
  rw [he] at h
  linarith [Real.exp_le_exp.mpr hfar]

/-- A positive physical pressure lower bound for the explicit HS construction.
The half-mass hypothesis is the actual planted typicality statement that must
be proved by the latitude RS interpolation argument. -/
theorem pressure_lower_of_hs_planted_half {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β δ η ε : ℝ} (hβ : 0 < β)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hε : 0 < ε)
    (hfirst : (1/2 : ℝ) ≤ (plantedLaw (N := N) (mixtureCoefficients μ) β).real
      (hsTruncation (mixtureCoefficients μ) β δ
        (annealedExponent N (mixtureCoefficients μ) β-(N : ℝ)*η)))
    (htail : 2*Real.exp (-(ε^2*(N : ℝ))/(2*β^2*μ.xi 1)) <
      Real.exp (-((N : ℝ)*β^2*μ.xi 1*δ^2))/32) :
    (annealedExponent N (mixtureCoefficients μ) β-Real.log 4)/(N : ℝ)-ε ≤
      quenchedPressure N μ β := by
  let c := mixtureCoefficients μ
  let A := annealedExponent N c β
  let K := (N : ℝ)*β^2*μ.xi 1*δ^2
  let T := hsTruncation (N := N) c β δ (A-(N : ℝ)*η)
  let Y := truncatedPartition c β T
  let a := Real.exp A/2
  let b := 2*Real.exp (2*A+K)
  have hc := mixtureCoefficients_nonnegative μ
  have hT : MeasurableSet T := hsTruncation_measurable c β δ _
  have hmean : a ≤ ∫ J, Y J ∂disorderLaw N μ.maxDegree := by
    have h := expected_truncatedPartition_lower hN c hc β hT hfirst
    simpa only [a,A,Y,one_div,div_eq_mul_inv,mul_comm,one_mul] using h
  have hsecond : (∫ J, Y J^2 ∂disorderLaw N μ.maxDegree) ≤ b := by
    have h := expected_hsTruncatedPartition_sq_gap_le hN c hc β hδ hδ1 hη
    rw [covariancePolynomial_mixture] at h
    exact h
  have hr : a^2/(4*b)=Real.exp (-K)/32 := by
    have hApos : Real.exp A ≠ 0 := (Real.exp_pos _).ne'
    have hKpos : Real.exp K ≠ 0 := (Real.exp_pos _).ne'
    dsimp only [a,b]
    rw [Real.exp_add,show 2*A=A+A by ring,Real.exp_add,Real.exp_neg]
    field_simp
    ring
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  apply SphericalMomentLower.pressure_lower_of_truncated_partition_moments hN μ hβ Y
    (truncatedPartition_measurable c β hT)
    (truncatedPartition_sq_integrable hN c hc β hT)
    (.of_forall (fun J => truncatedPartition_nonneg c β T J))
    (.of_forall (fun J => truncatedPartition_le_partition hN c β hT J))
    (show 0 < a by dsimp [a]; positivity) (show 0 < b by dsimp [b]; positivity)
    hmean hsecond ((A-Real.log 4)/(N : ℝ)) ε hε ?_ ?_
  · rw [mul_div_cancel₀ _ hNr.ne']
    have he : a/2=Real.exp A/4 := by dsimp [a]; ring
    rw [he,Real.log_div (Real.exp_pos _).ne' (by norm_num : (4 : ℝ) ≠ 0),Real.log_exp]
  · rw [hr]
    exact htail

end SlowEquilibration.SphericalModel
