-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTruncatedFeatureMoment

@[expose] public section

/-! Actual normalized truncated-feature second moments, obtained by integrating
the literal vector HS split and the exact Gaussian pair exponential moment. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem hsTruncatedFeatureMean_sq_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β) (δ L : ℝ) :
    Integrable (fun J : Disorder N P => ‖truncatedFeatureMean c β (hsTruncation c β δ L) J‖^2)
      (disorderLaw N P) := by
  have hiW : Integrable (weightedOverlapPairPartition (N:=N) c β δ) (disorderLaw N P) :=
    (weighted_overlap_pair_prod_integrable hN c hc β δ).integral_prod_left
  have hiZ : Integrable (fun J : Disorder N P => partition N β (field c J)) (disorderLaw N P) :=
    (field_exp_prod_integrable hN c hc β).integral_prod_left
  apply ((hiW.const_mul (β^2)).add (hiZ.const_mul
    (β^2*(N:ℝ)*covariancePolynomial c 1*Real.exp L))).mono'
  · exact ((truncatedFeatureMean_measurable c β (hsTruncation_measurable c β δ L)).norm.pow_const 2).aestronglyMeasurable
  · exact .of_forall fun J => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hsTruncatedFeatureMean_sq_le hN c hc hβ δ L J

theorem normalized_hsTruncatedFeatureMean_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β) (δ η : ℝ) :
    Integrable (fun J : Disorder N P => ‖Real.exp (-annealedExponent N c β) •
      truncatedFeatureMean c β (hsTruncation c β δ
        (annealedExponent N c β-(N:ℝ)*η)) J‖^2) (disorderLaw N P) := by
  have hi := hsTruncatedFeatureMean_sq_integrable hN c hc hβ δ
    (annealedExponent N c β-(N:ℝ)*η)
  convert hi.const_mul ((Real.exp (-annealedExponent N c β))^2) using 1
  funext J
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow]

/-- The actual feature-barycenter moment has a bounded central contribution
and an exponentially small far contribution even in the quadratic model. -/
theorem normalized_hsTruncatedFeatureMean_second_moment_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β) (δ η : ℝ) :
    (∫J : Disorder N P,‖Real.exp (-annealedExponent N c β) •
      truncatedFeatureMean c β (hsTruncation c β δ
        (annealedExponent N c β-(N:ℝ)*η)) J‖^2 ∂disorderLaw N P) ≤
      β^2*weightedCentralOverlapMoment N c β δ+
        β^2*(N:ℝ)*covariancePolynomial c 1*Real.exp (-(N:ℝ)*η) := by
  let A := annealedExponent N c β
  let L := A-(N:ℝ)*η
  let T := hsTruncation (N:=N) c β δ L
  have hiW : Integrable (weightedOverlapPairPartition (N:=N) c β δ) (disorderLaw N P) :=
    (weighted_overlap_pair_prod_integrable hN c hc β δ).integral_prod_left
  have hiZ : Integrable (fun J : Disorder N P => partition N β (field c J)) (disorderLaw N P) :=
    (field_exp_prod_integrable hN c hc β).integral_prod_left
  have hh := integral_mono (hsTruncatedFeatureMean_sq_integrable hN c hc hβ δ L)
    ((hiW.const_mul (β^2)).add (hiZ.const_mul (β^2*(N:ℝ)*covariancePolynomial c 1*Real.exp L)))
    (hsTruncatedFeatureMean_sq_le hN c hc hβ δ L)
  dsimp only [Pi.add_apply] at hh
  rw [integral_add (hiW.const_mul _) (hiZ.const_mul _),integral_const_mul,integral_const_mul,
    expected_weightedOverlapPairPartition_eq hN c hc β δ,expected_partition hN c hc β] at hh
  rw [show (N:ℝ)*β^2*covariancePolynomial c 1/2=annealedExponent N c β from rfl] at hh
  have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg (Real.exp (-A)))
  have he : (fun J : Disorder N P => ‖Real.exp (-A) • truncatedFeatureMean c β T J‖^2)=
      fun J => (Real.exp (-A))^2*‖truncatedFeatureMean c β T J‖^2 := by
    funext J
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow]
  change (∫J : Disorder N P,‖Real.exp (-A) • truncatedFeatureMean c β T J‖^2 ∂disorderLaw N P) ≤ _
  rw [he,integral_const_mul]
  convert hs using 1
  symm
  dsimp only [A,L]
  rw [pow_two,← Real.exp_add,mul_add]
  have hcancel : Real.exp (-annealedExponent N c β+-annealedExponent N c β)*
      Real.exp (2*annealedExponent N c β)=1 := by rw [← Real.exp_add]; ring_nf; simp
  have hfar : Real.exp (-annealedExponent N c β+-annealedExponent N c β)*
      (Real.exp (annealedExponent N c β-(N:ℝ)*η)*Real.exp (annealedExponent N c β))=
      Real.exp (-(N:ℝ)*η) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  calc
    _ = β^2*weightedCentralOverlapMoment N c β δ*
      (Real.exp (-annealedExponent N c β+-annealedExponent N c β)*Real.exp (2*annealedExponent N c β))+
      β^2*(N:ℝ)*covariancePolynomial c 1*
        (Real.exp (-annealedExponent N c β+-annealedExponent N c β)*
          (Real.exp (annealedExponent N c β-(N:ℝ)*η)*Real.exp (annealedExponent N c β))) := by ring
    _ = _ := by rw [hcancel,hfar]; simp

end SlowEquilibration.SphericalModel
