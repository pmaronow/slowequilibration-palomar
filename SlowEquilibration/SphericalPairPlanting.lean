-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedShift

@[expose] public section

/-!
# Actual two-point planting for the spherical Gaussian mixture

The pair covariance, translation vector and ordinary Gaussian event probability
are computed from the actual disorder law. These identities supply the genuine
integrand of a truncated second moment. No overlap-tail or critical-count
asymptotic estimate is assumed or asserted.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped Topology

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem plantedShift_pair_add {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u v : Vector N) :
    gaussianLinearCovarianceShift (disorderLaw N P)
      (β • (fieldCLM c u+fieldCLM c v)) =
      plantedShift c β u+plantedShift c β v := by
  have hu : Integrable (fun J : Disorder N P => (β*field c J u) • J) (disorderLaw N P) := by
    have hm : MemLp (fun J : Disorder N P => (β*field c J u) • J) 1 (disorderLaw N P) :=
      ((field_memLp c u).const_mul β).smul IsGaussian.memLp_two_id
    exact hm.integrable (by norm_num)
  have hv : Integrable (fun J : Disorder N P => (β*field c J v) • J) (disorderLaw N P) := by
    have hm : MemLp (fun J : Disorder N P => (β*field c J v) • J) 1 (disorderLaw N P) :=
      ((field_memLp c v).const_mul β).smul IsGaussian.memLp_two_id
    exact hm.integrable (by norm_num)
  simp only [plantedShift,gaussianLinearCovarianceShift,smul_apply,add_apply,fieldCLM_apply,smul_eq_mul]
  rw [← integral_add hu hv]
  apply integral_congr_ae
  exact .of_forall fun J => by simp only [mul_add,add_smul]

/-- The exact pair variance, including both actual self-covariances and the
actual overlap covariance. -/
theorem plantedShift_pair_secondMoment {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (u v : Vector N) (hu : ‖u‖^2=(N : ℝ)) (hv : ‖v‖^2=(N : ℝ)) :
    gaussianLinearSecondMoment (disorderLaw N P) (β • (fieldCLM c u+fieldCLM c v)) =
      2*(N : ℝ)*β^2*(covariancePolynomial c 1+covariancePolynomial c (overlap u v)) := by
  have hNp : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hiu := (field_memLp c u).integrable_mul (field_memLp c u)
  have hiv := (field_memLp c v).integrable_mul (field_memLp c v)
  have hiuv := (field_memLp c u).integrable_mul (field_memLp c v)
  have hsum : (∫ J : Disorder N P,
      (field c J u*field c J u+2*(field c J u*field c J v))+field c J v*field c J v
      ∂disorderLaw N P) =
      (∫ J : Disorder N P, field c J u*field c J u+2*(field c J u*field c J v) ∂disorderLaw N P)+
        ∫ J : Disorder N P, field c J v*field c J v ∂disorderLaw N P := by
    simpa only [Pi.add_apply,Pi.mul_apply] using integral_add (hiu.add (hiuv.const_mul 2)) hiv
  have hsum' : (∫ J : Disorder N P,
      field c J u*field c J u+2*(field c J u*field c J v) ∂disorderLaw N P) =
      (∫ J : Disorder N P, field c J u*field c J u ∂disorderLaw N P)+
        ∫ J : Disorder N P, 2*(field c J u*field c J v) ∂disorderLaw N P := by
    simpa only [Pi.add_apply,Pi.mul_apply] using integral_add hiu (hiuv.const_mul 2)
  unfold gaussianLinearSecondMoment
  simp only [smul_apply,add_apply,fieldCLM_apply,smul_eq_mul]
  have he : (fun J : Disorder N P => (β*(field c J u+field c J v))^2) =
      fun J => β^2*((field c J u*field c J u+2*(field c J u*field c J v))+
        field c J v*field c J v) := by
    funext J
    ring
  rw [he, integral_const_mul, hsum, hsum', integral_const_mul,
    field_product_integral hNp c hc, field_product_integral hNp c hc,
    field_product_integral hNp c hc, overlap_self hNp u hu, overlap_self hNp v hv]
  ring

/-- Genuine whole-disorder Cameron--Martin planting at two sphere points. -/
theorem pair_exponential_shift_integral {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (u v : Vector N) (hu : ‖u‖^2=(N : ℝ)) (hv : ‖v‖^2=(N : ℝ))
    (F : Disorder N P → ℝ) (hF : Measurable F) :
    (∫ J, F J*Real.exp (β*(field c J u+field c J v)) ∂disorderLaw N P) =
      Real.exp ((N : ℝ)*β^2*(covariancePolynomial c 1+covariancePolynomial c (overlap u v)))*
        ∫ J, F (J+plantedShift c β u+plantedShift c β v) ∂disorderLaw N P := by
  have h := gaussian_linear_exponential_shift (disorderLaw N P) (disorder_mean N P)
    (β • (fieldCLM c u+fieldCLM c v)) F hF
  rw [plantedShift_pair_secondMoment hN c hc β u v hu hv, plantedShift_pair_add] at h
  simp only [smul_apply,add_apply,fieldCLM_apply,smul_eq_mul] at h
  convert h using 1; simp only [add_assoc]
  congr 2
  ring

/-- The physical mixed field after pair planting has the exact sum of the
two overlap profiles, on the whole ambient space. -/
theorem field_add_pairPlantedShift {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (u v x : Vector N) (J : Disorder N P) :
    field c (J+plantedShift c β u+plantedShift c β v) x =
      field c J x+β*(N : ℝ)*(covariancePolynomial c (overlap x u)+covariancePolynomial c (overlap x v)) := by
  rw [field_add_plantedShift hN c hc β v x,
    field_add_plantedShift hN c hc β u x]
  ring

/-- The literal two-point truncated exponential moment under the original
disorder equals the exact overlap weight times a genuine translated Gaussian
event probability. -/
theorem pair_truncated_exponential_moment {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (u v : Vector N) (hu : ‖u‖^2=(N : ℝ)) (hv : ‖v‖^2=(N : ℝ))
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    (∫ J : Disorder N P,
      T.indicator (fun z => Real.exp (β*field c z.1 z.2)) (J,u)*
      T.indicator (fun z => Real.exp (β*field c z.1 z.2)) (J,v) ∂disorderLaw N P) =
      Real.exp ((N : ℝ)*β^2*(covariancePolynomial c 1+covariancePolynomial c (overlap u v)))*
        (disorderLaw N P).real {J | (J+plantedShift c β u+plantedShift c β v,u) ∈ T ∧
          (J+plantedShift c β u+plantedShift c β v,v) ∈ T} := by
  let A : Set (Disorder N P) := {J | (J,u) ∈ T ∧ (J,v) ∈ T}
  let F : Disorder N P → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hA : MeasurableSet A :=
    (hT.preimage (measurable_id.prodMk measurable_const)).inter
      (hT.preimage (measurable_id.prodMk measurable_const))
  have hF : Measurable F := measurable_const.indicator hA
  have he : (fun J : Disorder N P =>
      T.indicator (fun z => Real.exp (β*field c z.1 z.2)) (J,u)*
      T.indicator (fun z => Real.exp (β*field c z.1 z.2)) (J,v)) =
      fun J => F J*Real.exp (β*(field c J u+field c J v)) := by
    funext J
    by_cases hJu : (J,u) ∈ T <;> by_cases hJv : (J,v) ∈ T <;>
      simp [F,A,hJu,hJv, mul_add,Real.exp_add]
  rw [he, pair_exponential_shift_integral hN c hc β u v hu hv F hF]
  congr 1
  let B : Set (Disorder N P) := {J | (J+plantedShift c β u+plantedShift c β v,u) ∈ T ∧
    (J+plantedShift c β u+plantedShift c β v,v) ∈ T}
  have hB : MeasurableSet B :=
    (hT.preimage (((measurable_id.add measurable_const).add measurable_const).prodMk measurable_const)).inter
      (hT.preimage (((measurable_id.add measurable_const).add measurable_const).prodMk measurable_const))
  have hf : (fun J : Disorder N P => F (J+plantedShift c β u+plantedShift c β v)) =
      B.indicator (fun _ => (1 : ℝ)) := by
    funext J
    by_cases hJu : (J+plantedShift c β u+plantedShift c β v,u) ∈ T <;>
      by_cases hJv : (J+plantedShift c β u+plantedShift c β v,v) ∈ T <;>
        simp [F,B,A,hJu,hJv]
  rw [hf, integral_indicator hB]
  simp [B]

end SlowEquilibration.SphericalModel
