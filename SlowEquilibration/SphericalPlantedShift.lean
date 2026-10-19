-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PlantedLaw
public import FourPapersCommon.GaussianLinearCameronMartin

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped Topology

instance disorderLaw_Gaussian (N P : ℕ) : IsGaussian (disorderLaw N P) := by
  simpa only [Measure.map_id] using (disorder_hasGaussianLaw N P).isGaussian_map

theorem disorder_mean (N P : ℕ) :
    (∫ J : Disorder N P,J ∂disorderLaw N P)=0 := by
  funext p I
  let projp : Disorder N P →L[ℝ] SphericalAging.FiniteModel.Disorder N p.val.val :=
    ContinuousLinearMap.proj p
  let projI : SphericalAging.FiniteModel.Disorder N p.val.val →L[ℝ] ℝ :=
    ContinuousLinearMap.proj I
  let L : Disorder N P →L[ℝ] ℝ := projI.comp projp
  have h := L.integral_comp_comm (IsGaussian.integrable_id (μ:=disorderLaw N P))
  change (∫ J : Disorder N P,J p I ∂disorderLaw N P)=
    (∫ J : Disorder N P,J ∂disorderLaw N P) p I at h
  rw [←h]
  have hl := (SphericalAging.FiniteModel.coordinate_hasLaw N p.val.val I).fun_comp
    (degree_block_hasLaw (N:=N) p)
  rw [hl.integral_eq,integral_id_gaussianReal]
  rfl

/-- The literal disorder-space covariance shift used for the planted law. -/
def plantedShift {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) (u : Vector N) : Disorder N P :=
  gaussianLinearCovarianceShift (disorderLaw N P) (β • fieldCLM c u)

theorem plantedShift_field {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) (u x : Vector N) :
    field c (plantedShift c β u) x = β*(N:ℝ)*covariancePolynomial c (overlap x u) := by
  have hi : Integrable (fun J : Disorder N P => (β*field c J u) • J) (disorderLaw N P) := by
    have hm : MemLp (fun J : Disorder N P => (β*field c J u) • J) 1 (disorderLaw N P) :=
      ((field_memLp c u).const_mul β).smul IsGaussian.memLp_two_id
    exact hm.integrable (by norm_num)
  have h := (fieldCLM c x).integral_comp_comm hi
  have hs : plantedShift c β u =
      ∫ J : Disorder N P,(β*field c J u) • J ∂disorderLaw N P := by
    simp only [plantedShift,gaussianLinearCovarianceShift,smul_apply,fieldCLM_apply,smul_eq_mul]
  rw [hs,←fieldCLM_apply,←h]
  simp only [map_smul,fieldCLM_apply,smul_eq_mul]
  have heq : (fun J : Disorder N P => β*field c J u*field c J x)=
      fun J => β*(field c J x*field c J u) := by funext J;ring
  rw [heq,integral_const_mul,field_product_integral (lt_of_lt_of_le Nat.zero_lt_one hN) c hc]
  ring

theorem field_add_plantedShift {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) (u x : Vector N) (J : Disorder N P) :
    field c (J+plantedShift c β u) x=
      field c J x+β*(N:ℝ)*covariancePolynomial c (overlap x u) := by
  rw [←fieldCLM_apply, map_add,fieldCLM_apply,fieldCLM_apply,
    plantedShift_field hN c hc β u x]

theorem plantedShift_secondMoment {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ)
    (u : Vector N) (hu : ‖u‖^2=(N:ℝ)) :
    gaussianLinearSecondMoment (disorderLaw N P) (β • fieldCLM c u)=
      (N:ℝ)*β^2*covariancePolynomial c 1 := by
  unfold gaussianLinearSecondMoment
  simp only [smul_apply,fieldCLM_apply,smul_eq_mul,mul_pow]
  rw [integral_const_mul]
  have heq : (fun J : Disorder N P => field c J u^2)=fun J=>field c J u*field c J u := by
    funext J;ring
  rw [heq,field_product_integral (lt_of_lt_of_le Nat.zero_lt_one hN) c hc,
    overlap_self (lt_of_lt_of_le Nat.zero_lt_one hN) u hu]
  ring

/-- The entire disorder law under the actual exponential tilt is the
original Gaussian law translated by its true covariance vector. -/
theorem planted_disorder_shift_integral {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ)
    (u : Vector N) (hu : ‖u‖^2=(N:ℝ))
    (F : Disorder N P → ℝ) (hF : Measurable F) :
    (∫ J : Disorder N P,F J*plantedDensity c β (J,u) ∂disorderLaw N P)=
      ∫ J : Disorder N P,F (J+plantedShift c β u) ∂disorderLaw N P := by
  have h := gaussian_linear_cameronMartin_borel (disorderLaw N P) (disorder_mean N P)
    (β • fieldCLM c u) F hF
  rw [plantedShift_secondMoment hN c hc β u hu] at h
  simpa only [plantedDensity,plantedShift,annealedExponent,smul_apply,
    fieldCLM_apply,smul_eq_mul] using h.symm

/-- The field under planting is the original actual mixed field plus the
manuscript's deterministic overlap profile, for arbitrary Borel whole-field tests. -/
theorem planted_wholeField_shift {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ)
    (u : Vector N) (hu : ‖u‖^2=(N:ℝ))
    (F : (Vector N → ℝ) → ℝ) (hF : Measurable F) :
    (∫ J : Disorder N P,F (fun x => field c J x)*plantedDensity c β (J,u) ∂disorderLaw N P)=
      ∫ J : Disorder N P,F (fun x => field c J x+
        β*(N:ℝ)*covariancePolynomial c (overlap x u)) ∂disorderLaw N P := by
  have h := planted_disorder_shift_integral hN c hc β u hu
    (fun J : Disorder N P => F (fun x => field c J x))
    (hF.comp (measurable_fieldFunction c))
  apply h.trans
  congr 1
  funext J
  congr 1
  funext x
  exact field_add_plantedShift hN c hc β u x J

end
end SlowEquilibration.SphericalModel
