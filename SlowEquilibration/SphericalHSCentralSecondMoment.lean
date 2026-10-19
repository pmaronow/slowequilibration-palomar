-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalHSTruncation

@[expose] public section

/-! # Exact central-overlap term of the actual HS second moment

The spherical pair integral is retained exactly, including the signed
covariance polynomial. No asymptotic estimate is assumed.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual small-overlap spherical pair expectation after dividing the
annealed pair exponential by its true self-covariance factor. -/
def centralOverlapMoment {P : ℕ} (N : ℕ) (c : Degree P → ℝ) (β δ : ℝ) : ℝ :=
  ∫ z : Vector N × Vector N,
    (smallOverlap δ).indicator (fun w => Real.exp ((N:ℝ)*β^2*covariancePolynomial c (overlap w.1 w.2))) z
      ∂(sphereLaw N).prod (sphereLaw N)

theorem expected_smallOverlapPairPartition_eq {N P : ℕ} (hN : 1≤N)
    (c : Degree P → ℝ) (hc : ∀ p, 0≤c p) (β δ : ℝ) :
    (∫ J, overlapPairPartition c β (smallOverlap δ) J ∂disorderLaw N P)=
      Real.exp (2*annealedExponent N c β)*centralOverlapMoment N c β δ := by
  have hi := overlap_pair_prod_integrable hN c hc β (smallOverlap_measurable δ)
  unfold overlapPairPartition centralOverlapMoment
  rw [integral_integral_swap hi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sphereLaw_pair_support hN] with z hz
  by_cases hs : z∈smallOverlap δ
  · simp only [Set.indicator_of_mem hs]
    have hpair := pair_truncated_exponential_moment hN c hc β z.1 z.2 hz.1 hz.2
      (T := Set.univ) MeasurableSet.univ
    simp only [Set.indicator_univ,Set.mem_univ,and_self,Set.ofPred_true,probReal_univ,mul_one] at hpair
    rw [hpair,← Real.exp_add]
    congr 1
    unfold annealedExponent
    ring
  · simp only [Set.indicator_of_notMem hs,integral_zero,mul_zero]

/-- The actual normalized HS second moment has the exact central-overlap
term and an exponentially vanishing far-overlap error. -/
theorem normalized_hsTruncatedPartition_second_moment_le {N P : ℕ} (hN : 1≤N)
    (c : Degree P → ℝ) (hc : ∀ p, 0≤c p) (β δ η : ℝ) :
    (∫ J, (Real.exp (-annealedExponent N c β)*truncatedPartition c β
      (hsTruncation c β δ (annealedExponent N c β-(N:ℝ)*η)) J)^2 ∂disorderLaw N P) ≤
      centralOverlapMoment N c β δ+Real.exp (-(N:ℝ)*η) := by
  let A := annealedExponent N c β
  let T := hsTruncation (N := N) c β δ (A-(N:ℝ)*η)
  have hT := hsTruncation_measurable (N := N) c β δ (A-(N:ℝ)*η)
  have hiY := truncatedPartition_sq_integrable hN c hc β hT
  have hiS := overlapPairPartition_integrable hN c hc β (smallOverlap_measurable δ)
  have hiZ : Integrable (fun J : Disorder N P => partition N β (field c J)) (disorderLaw N P) :=
    (field_exp_prod_integrable hN c hc β).integral_prod_left
  have hle := integral_mono hiY (hiS.add (hiZ.const_mul (Real.exp (A-(N:ℝ)*η))))
    (hsTruncatedPartition_sq_le hN c β δ (A-(N:ℝ)*η))
  dsimp only [Pi.add_apply] at hle
  rw [integral_add hiS (hiZ.const_mul _),integral_const_mul,
    expected_smallOverlapPairPartition_eq hN c hc β δ,expected_partition hN c hc β] at hle
  have hscaled := mul_le_mul_of_nonneg_left hle (sq_nonneg (Real.exp (-A)))
  have hrewrite : (fun J : Disorder N P =>
      (Real.exp (-A)*truncatedPartition c β T J)^2)=
      fun J => (Real.exp (-A))^2*(truncatedPartition c β T J)^2 := by funext J; ring
  change (∫ J, (Real.exp (-A)*truncatedPartition c β T J)^2 ∂disorderLaw N P)≤_
  rw [hrewrite,integral_const_mul]
  convert hscaled using 1
  dsimp only [A,T]
  rw [pow_two,← Real.exp_add,mul_add,← mul_assoc,← Real.exp_add,← Real.exp_add,
    show -annealedExponent N c β + -annealedExponent N c β + 2*annealedExponent N c β=0 by ring,
    Real.exp_zero,one_mul,← Real.exp_add]
  congr 1
  unfold annealedExponent
  ring_nf

end
end SlowEquilibration.SphericalModel
