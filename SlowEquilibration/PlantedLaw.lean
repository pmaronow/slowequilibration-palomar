-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbs
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

/-- The annealed pressure normalization, evaluated from the proved Gaussian moment. -/
def annealedExponent {P : ℕ} (N : ℕ) (c : Degree P → ℝ) (β : ℝ) : ℝ :=
  (N:ℝ)*β^2*covariancePolynomial c 1/2

def plantedDensity {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (z : Disorder N P × Vector N) : ℝ :=
  Real.exp (β*field c z.1 z.2-annealedExponent N c β)

/-- The actual planted joint law, defined by exponential tilting of the
independent disorder and uniform sphere laws. -/
def plantedLaw {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measure (Disorder N P × Vector N) :=
  ((disorderLaw N P).prod (sphereLaw N)).withDensity
    (fun z => ENNReal.ofReal (plantedDensity c β z))

/-- The actual Gibbs-reference joint law with the quenched Gibbs density. -/
def gibbsReferenceLaw {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measure (Disorder N P × Vector N) :=
  ((disorderLaw N P).prod (sphereLaw N)).withDensity
    (fun z => ENNReal.ofReal (gibbsDensity N β (field c z.1) z.2))

def likelihood {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) (J : Disorder N P) : ℝ :=
  partition N β (field c J)*Real.exp (-annealedExponent N c β)

theorem plantedDensity_continuous {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Continuous (plantedDensity (N:=N) c β) :=
  Real.continuous_exp.comp ((continuous_const.mul (field_jointContinuous c)).sub continuous_const)

theorem partition_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measurable (fun J : Disorder N P => partition N β (field c J)) := by
  have h : StronglyMeasurable (fun z : Disorder N P × Vector N =>
      Real.exp (β*field c z.1 z.2)) :=
    (Real.continuous_exp.comp (continuous_const.mul (field_jointContinuous c))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem gibbsReferenceDensity_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measurable (fun z : Disorder N P × Vector N => gibbsDensity N β (field c z.1) z.2) := by
  exact (Real.continuous_exp.comp (continuous_const.mul (field_jointContinuous c))).measurable.div
    ((partition_measurable c β).comp measurable_fst)

theorem likelihood_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measurable (likelihood (N:=N) c β) := (partition_measurable c β).mul_const _

theorem likelihood_pos {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β : ℝ) (J : Disorder N P) : 0 < likelihood c β J :=
  mul_pos (partition_pos hN β (field_contDiff c J).continuous) (Real.exp_pos _)

theorem plantedDensity_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) :
    Integrable (plantedDensity c β) ((disorderLaw N P).prod (sphereLaw N)) := by
  have h := (field_exp_prod_integrable hN c hc β).mul_const
    (Real.exp (-annealedExponent N c β))
  convert h using 1
  funext z
  simp [plantedDensity,Real.exp_sub,Real.exp_neg,div_eq_mul_inv]

theorem integral_plantedDensity {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) :
    (∫ z,plantedDensity c β z ∂((disorderLaw N P).prod (sphereLaw N)))=1 := by
  have heq : plantedDensity (N:=N) c β = fun z : Disorder N P × Vector N =>
      Real.exp (β*field c z.1 z.2)*Real.exp (-annealedExponent N c β) := by
    funext z
    simp [plantedDensity,Real.exp_sub,Real.exp_neg,div_eq_mul_inv]
  rw [heq,integral_mul_const,integral_prod _ (field_exp_prod_integrable hN c hc β)]
  change (∫ J : Disorder N P,partition N β (field c J) ∂disorderLaw N P)*_=1
  rw [expected_partition hN c hc β]
  simp [annealedExponent,Real.exp_neg]

theorem plantedLaw_probability {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) :
    IsProbabilityMeasure (plantedLaw (N:=N) c β) := by
  constructor
  rw [plantedLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (plantedDensity_integrable hN c hc β)
      (Eventually.of_forall (fun z => (Real.exp_pos _).le)),integral_plantedDensity hN c hc β]
  norm_num

theorem gibbsReferenceDensity_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    Integrable (fun z : Disorder N P × Vector N => gibbsDensity N β (field c z.1) z.2)
      ((disorderLaw N P).prod (sphereLaw N)) := by
  apply (integrable_prod_iff (gibbsReferenceDensity_measurable c β).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun J => gibbsDensity_integrable hN β (field_contDiff c J).continuous),?_⟩
  have heq : (fun J : Disorder N P => ∫ x,‖gibbsDensity N β (field c J) x‖ ∂sphereLaw N)=
      fun _ => (1:ℝ) := by
    funext J
    simp only [Real.norm_eq_abs,abs_of_pos (gibbsDensity_pos hN β (field_contDiff c J).continuous _)]
    exact integral_gibbsDensity hN β (field_contDiff c J).continuous
  rw [heq]
  exact integrable_const 1

theorem integral_gibbsReferenceDensity {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    (∫ z : Disorder N P × Vector N,gibbsDensity N β (field c z.1) z.2
      ∂((disorderLaw N P).prod (sphereLaw N)))=1 := by
  rw [integral_prod _ (gibbsReferenceDensity_integrable hN c β)]
  simp only [integral_gibbsDensity hN β (field_contDiff c _).continuous]
  simp

theorem gibbsReferenceLaw_probability {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) : IsProbabilityMeasure (gibbsReferenceLaw (N:=N) c β) := by
  constructor
  rw [gibbsReferenceLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (gibbsReferenceDensity_integrable hN c β)
      (Eventually.of_forall (fun z => (gibbsDensity_pos hN β (field_contDiff c z.1).continuous z.2).le)),
    integral_gibbsReferenceDensity hN c β]
  norm_num

/-- The likelihood identity is an equality of the actual joint measures. -/
theorem planted_eq_gibbsReference_withDensity {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    plantedLaw c β=(gibbsReferenceLaw c β).withDensity
      (fun z : Disorder N P × Vector N => ENNReal.ofReal (likelihood c β z.1)) := by
  have hd : Measurable (fun z : Disorder N P × Vector N =>
      ENNReal.ofReal (gibbsDensity N β (field c z.1) z.2)) :=
    (gibbsReferenceDensity_measurable c β).ennreal_ofReal
  have hl : Measurable (fun z : Disorder N P × Vector N =>
      ENNReal.ofReal (likelihood c β z.1)) :=
    ((likelihood_measurable c β).comp measurable_fst).ennreal_ofReal
  rw [gibbsReferenceLaw,←withDensity_mul _ hd hl]
  unfold plantedLaw
  congr 1
  funext z
  dsimp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (gibbsDensity_pos hN β (field_contDiff c z.1).continuous z.2).le]
  congr 1
  unfold plantedDensity likelihood gibbsDensity
  rw [Real.exp_sub,Real.exp_neg]
  have hZ : partition N β (field c z.1) ≠ 0 :=
    (partition_pos hN β (field_contDiff c z.1).continuous).ne'
  field_simp

theorem plantedDensity_integral_disorder {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    (∫ J : Disorder N P,plantedDensity c β (J,x) ∂disorderLaw N P)=1 := by
  have heq : (fun J : Disorder N P => plantedDensity c β (J,x))=
      fun J => Real.exp (β*field c J x)*Real.exp (-annealedExponent N c β) := by
    funext J
    simp [plantedDensity,Real.exp_sub,Real.exp_neg,div_eq_mul_inv]
  rw [heq,integral_mul_const,
    field_exp_integral_on_sphere (lt_of_lt_of_le Nat.zero_lt_one hN) c hc x hx β]
  simp [annealedExponent,Real.exp_neg]

/-- Every bounded continuous reference observable has precisely its uniform
sphere expectation under the actual planted joint law. -/
theorem planted_reference_expectation {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) (f : Vector N →ᵇ ℝ) :
    (∫ z : Disorder N P × Vector N,f z.2 ∂plantedLaw c β)=∫ x,f x ∂sphereLaw N := by
  have hweight := plantedDensity_integrable hN c hc β
  have hint : Integrable (fun z : Disorder N P × Vector N => plantedDensity c β z*f z.2)
      ((disorderLaw N P).prod (sphereLaw N)) :=
    hweight.mul_bdd (f.continuous.comp continuous_snd).aestronglyMeasurable
      (Eventually.of_forall (fun z => f.norm_coe_le_norm z.2))
  rw [plantedLaw,integral_withDensity_eq_integral_toReal_smul
    (plantedDensity_continuous c β).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun z : Disorder N P × Vector N =>
      (ENNReal.ofReal (plantedDensity c β z)).toReal • f z.2)=
      fun z => plantedDensity c β z*f z.2 := by
    funext z
    rw [ENNReal.toReal_ofReal (show 0 ≤ plantedDensity c β z from (Real.exp_pos _).le),
      smul_eq_mul]
  rw [heq]
  rw [integral_prod_symm _ hint]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  rw [integral_mul_const,plantedDensity_integral_disorder hN c hc β x hx,one_mul]

/-- The u-marginal of the planted joint measure is the actual uniform
radius-sqrt(N) sphere law. -/
theorem planted_reference_marginal {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) :
    (plantedLaw (N:=N) c β).map Prod.snd=sphereLaw N := by
  have := plantedLaw_probability hN c hc β
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
  exact planted_reference_expectation hN c hc β f

/-- Every bounded continuous disorder observable retains its original
expectation under the actual Gibbs-reference joint law. -/
theorem gibbsReference_disorder_expectation {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) (f : Disorder N P →ᵇ ℝ) :
    (∫ z : Disorder N P × Vector N,f z.1 ∂gibbsReferenceLaw c β)=
      ∫ J,f J ∂disorderLaw N P := by
  have hint : Integrable (fun z : Disorder N P × Vector N =>
      gibbsDensity N β (field c z.1) z.2*f z.1)
      ((disorderLaw N P).prod (sphereLaw N)) :=
    (gibbsReferenceDensity_integrable hN c β).mul_bdd
      (f.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => f.norm_coe_le_norm z.1))
  rw [gibbsReferenceLaw,integral_withDensity_eq_integral_toReal_smul
    (gibbsReferenceDensity_measurable c β).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun z : Disorder N P × Vector N =>
      (ENNReal.ofReal (gibbsDensity N β (field c z.1) z.2)).toReal • f z.1)=
      fun z => gibbsDensity N β (field c z.1) z.2*f z.1 := by
    funext z
    rw [ENNReal.toReal_ofReal (gibbsDensity_pos hN β (field_contDiff c z.1).continuous z.2).le,
      smul_eq_mul]
  rw [heq,integral_prod _ hint]
  congr 1
  funext J
  dsimp only
  rw [integral_mul_const,integral_gibbsDensity hN β (field_contDiff c J).continuous,one_mul]

theorem gibbsReference_disorder_marginal {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    (gibbsReferenceLaw (N:=N) c β).map Prod.fst=disorderLaw N P := by
  have := gibbsReferenceLaw_probability hN c β
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
  exact gibbsReference_disorder_expectation hN c β f

theorem planted_gibbsReference_mutual_ac {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    plantedLaw (N:=N) c β ≪ gibbsReferenceLaw c β ∧
      gibbsReferenceLaw (N:=N) c β ≪ plantedLaw c β := by
  rw [planted_eq_gibbsReference_withDensity hN c β]
  refine ⟨withDensity_absolutelyContinuous _ _,?_⟩
  apply withDensity_absolutelyContinuous'
  · exact (((likelihood_measurable (N:=N) c β).comp measurable_fst).ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall (fun z => (ENNReal.ofReal_pos.mpr (likelihood_pos hN c β z.1)).ne')

/-- The manuscript's Radon--Nikodym likelihood is computed from the
ordinary joint measures, with no derivative identity as a premise. -/
theorem planted_gibbsReference_rnDeriv {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) :
    (plantedLaw (N:=N) c β).rnDeriv (gibbsReferenceLaw c β) =ᵐ[gibbsReferenceLaw c β]
      fun z => ENNReal.ofReal (likelihood c β z.1) := by
  have := gibbsReferenceLaw_probability hN c β
  rw [planted_eq_gibbsReference_withDensity hN c β]
  exact Measure.rnDeriv_withDensity _
    ((likelihood_measurable (N:=N) c β).comp measurable_fst).ennreal_ofReal

end
end SlowEquilibration.SphericalModel
