module

public import SphericalAging.FiniteModel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi

public section

/-!
# Gaussian integration by parts for the actual ordered tensor law

The one-dimensional identity is derived from the actual Gaussian density and
improper integration by parts. The finite product identity uses Fubini and a
measure-preserving separation of the selected tensor coordinate. The hypotheses
are differentiability and integrability, rather than a Stein-identity premise.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SphericalAging.GaussianIntegrationByParts
open FiniteModel

theorem standardGaussian_integrable_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x*f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [toReal_gaussianPDF,smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun x => gaussianPDF_lt_top)) :
      Integrable f (volume.withDensity (gaussianPDF 0 1)) ↔
        Integrable (fun x => (gaussianPDF 0 1 x).toReal • f x) volume)

theorem standardGaussian_density_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,sub_zero]
  convert ((((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)).exp.const_mul
    (Real.sqrt (2*Real.pi*1))⁻¹) using 1
  · funext y
    simp only [Pi.neg_apply,Pi.pow_apply,id_eq,mul_one]
  · simp only [Pi.neg_apply,Pi.pow_apply,id_eq,mul_one]
    ring

/-- The exact Stein identity under the real standard Gaussian probability measure. -/
theorem standardGaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hdf : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1)=(∫ x, f' x ∂gaussianReal 0 1) := by
  have hρf := standardGaussian_integrable_iff.mp hf
  have hρdf := standardGaussian_integrable_iff.mp hdf
  have hρxf := standardGaussian_integrable_iff.mp hxf
  have ha : Integrable ((fun x => gaussianPDFReal 0 1 x)*f') volume := hρdf
  have hb : Integrable ((fun x => -x*gaussianPDFReal 0 1 x)*f) volume := by
    apply hρxf.neg.congr (ae_of_all _ (fun x => ?_))
    dsimp
    ring
  have hc : Integrable ((fun x => gaussianPDFReal 0 1 x)*f) volume := hρf
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_derivative x) (fun x _ => hd x) ha hb hc
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul] at *
  have he : (∫ x : ℝ, -x*gaussianPDFReal 0 1 x*f x)=
      -(∫ x : ℝ, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he,neg_neg] at hibp
  exact hibp.symm

section FiniteProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] abbrev otherCoordinates (i : ι) := {j : ι // j ≠ i}

@[expose, instance_reducible] def equalCoordinateUnique (i : ι) : Unique {j : ι // j=i} :=
  { default := ⟨i,rfl⟩
    uniq := fun j => Subtype.ext j.property }

/-- Actual measurable separation of one coordinate of the ordered disorder. -/
@[expose] def coordinateSplit (i : ι) : (ι → ℝ) ≃ᵐ ℝ × (otherCoordinates i → ℝ) :=
  letI : Unique {j : ι // j=i} := equalCoordinateUnique i
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun j => j=i)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique (fun _ : {j : ι // j=i} => ℝ))
      (MeasurableEquiv.refl (otherCoordinates i → ℝ)))

theorem coordinateSplit_measurePreserving (i : ι) :
    MeasurePreserving (coordinateSplit i) (Measure.pi (fun _ : ι => gaussianReal 0 1))
      ((gaussianReal 0 1).prod (Measure.pi (fun _ : otherCoordinates i => gaussianReal 0 1))) := by
  let : Unique {j : ι // j=i} := equalCoordinateUnique i
  have hu : MeasurePreserving (MeasurableEquiv.piUnique (fun _ : {j : ι // j=i} => ℝ))
      (@Measure.pi {j : ι // j=i} (fun _ => ℝ) (Subtype.fintype (fun j : ι => j=i))
        (fun _ => inferInstance) (fun _ => gaussianReal 0 1)) (gaussianReal 0 1) := by
    convert measurePreserving_piUnique (fun _ : {j : ι // j=i} => gaussianReal 0 1) using 1
    congr 1
    exact Subsingleton.elim _ _
  exact (hu.prod (MeasurePreserving.id (Measure.pi (fun _ : otherCoordinates i => gaussianReal 0 1)))).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (fun j => j=i))

omit [Fintype ι] in
theorem coordinateSplit_symm_coordinate (i : ι) (x : ℝ) (K : otherCoordinates i → ℝ) :
    (coordinateSplit i).symm (x,K) i=x := by
  simp [coordinateSplit,MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,MeasurableEquiv.prodCongr,MeasurableEquiv.piUnique,Equiv.prodCongr,Equiv.piUnique]

omit [Fintype ι] in
theorem coordinateSplit_symm_update (i : ι) (x y : ℝ) (K : otherCoordinates i → ℝ) :
    Function.update ((coordinateSplit i).symm (x,K)) i y=(coordinateSplit i).symm (y,K) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [coordinateSplit_symm_coordinate]
  · simp [coordinateSplit,MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,MeasurableEquiv.prodCongr,MeasurableEquiv.piUnique,Equiv.prodCongr,Equiv.piUnique,hj]

/-- Finite-product Stein identity, with genuine coordinate derivatives and integrability. -/
theorem finiteGaussian_integration_by_parts (i : ι) {F dF : (ι → ℝ) → ℝ}
    (hd : ∀ J : ι → ℝ, ∀ x : ℝ, HasDerivAt (fun y => F (Function.update J i y))
      (dF (Function.update J i x)) x)
    (hf : Integrable F (Measure.pi (fun _ : ι => gaussianReal 0 1)))
    (hdf : Integrable dF (Measure.pi (fun _ : ι => gaussianReal 0 1)))
    (hxf : Integrable (fun J : ι → ℝ => J i*F J) (Measure.pi (fun _ : ι => gaussianReal 0 1))) :
    (∫ J : ι → ℝ, J i*F J ∂Measure.pi (fun _ : ι => gaussianReal 0 1))=
      (∫ J : ι → ℝ, dF J ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  let μ : Measure (otherCoordinates i → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  have hm := (coordinateSplit_measurePreserving i).symm
  have hfi := (hm.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hdfi := (hm.integrable_comp hdf.aestronglyMeasurable).mpr hdf
  have hxfi := (hm.integrable_comp hxf.aestronglyMeasurable).mpr hxf
  rw [← hm.integral_comp' (fun J => J i*F J),← hm.integral_comp' dF]
  change (∫ z, (((fun J : ι → ℝ => J i*F J) ∘ (coordinateSplit i).symm) z)
      ∂((gaussianReal 0 1).prod μ))=
    (∫ z, ((dF ∘ (coordinateSplit i).symm) z) ∂((gaussianReal 0 1).prod μ))
  rw [integral_prod_symm _ hxfi,integral_prod_symm _ hdfi]
  apply integral_congr_ae
  filter_upwards [hfi.prod_left_ae,hdfi.prod_left_ae,hxfi.prod_left_ae] with K hK hKd hKx
  have hderiv (x : ℝ) : HasDerivAt (fun y => F ((coordinateSplit i).symm (y,K)))
      (dF ((coordinateSplit i).symm (x,K))) x := by
    simpa only [coordinateSplit_symm_update] using hd ((coordinateSplit i).symm (0,K)) x
  have hh := standardGaussian_integration_by_parts hderiv hK hKd
    (by simpa only [Function.comp_apply,coordinateSplit_symm_coordinate] using hKx)
  simpa only [Function.comp_apply,coordinateSplit_symm_coordinate] using hh

end FiniteProduct

/-- The exact coefficientwise identity for the manuscript's nonsymmetrized Gaussian tensor. -/
theorem disorder_integration_by_parts {N p : ℕ} (I : TensorIndex N p)
    {F dF : Disorder N p → ℝ}
    (hd : ∀ J : Disorder N p, ∀ x : ℝ, HasDerivAt (fun y => F (Function.update J I y))
      (dF (Function.update J I x)) x)
    (hf : Integrable F (disorderLaw N p)) (hdf : Integrable dF (disorderLaw N p))
    (hIF : Integrable (fun J : Disorder N p => J I*F J) (disorderLaw N p)) :
    (∫ J : Disorder N p, J I*F J ∂disorderLaw N p)=
      (∫ J : Disorder N p, dF J ∂disorderLaw N p) :=
  finiteGaussian_integration_by_parts I hd hf hdf hIF

/-- Gaussian coefficient integration by parts with independent initial/Brownian randomness. -/
theorem disorder_integration_by_parts_with_randomness {N p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν] (I : TensorIndex N p)
    {F dF : Disorder N p × Ω → ℝ}
    (hd : ∀ ω : Ω, ∀ J : Disorder N p, ∀ x : ℝ,
      HasDerivAt (fun y => F (Function.update J I y,ω)) (dF (Function.update J I x,ω)) x)
    (hf : Integrable F ((disorderLaw N p).prod ν))
    (hdf : Integrable dF ((disorderLaw N p).prod ν))
    (hIF : Integrable (fun z : Disorder N p × Ω => z.1 I*F z) ((disorderLaw N p).prod ν)) :
    (∫ z : Disorder N p × Ω, z.1 I*F z ∂(disorderLaw N p).prod ν)=
      (∫ z : Disorder N p × Ω, dF z ∂(disorderLaw N p).prod ν) := by
  rw [integral_prod_symm _ hIF,integral_prod_symm _ hdf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae,hdf.prod_left_ae,hIF.prod_left_ae] with ω hω hωd hωI
  exact disorder_integration_by_parts I (hd ω) hω hωd hωI

/-- A single normalized ordered-tensor monomial, the coefficient of J_I in H_N. -/
@[expose] def hamiltonianCoefficient {N p : ℕ} (I : TensorIndex N p) (x : Vector N) : ℝ :=
  normalization N p*tensorMonomial x I

theorem hamiltonian_eq_sum_coefficients {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p J x=∑ I : TensorIndex N p, J I*hamiltonianCoefficient I x := by
  unfold Hamiltonian hamiltonianCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

/-- The actual finite-dimensional Gaussian energy identity before the flow derivative is substituted.
Every derivative is a genuine partial derivative of the Hamiltonian coefficient evaluated on X. -/
theorem gaussian_hamiltonian_energy_identity {N p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν]
    (X : Disorder N p × Ω → Vector N) (dF : TensorIndex N p → Disorder N p × Ω → ℝ)
    (hd : ∀ I : TensorIndex N p, ∀ ω : Ω, ∀ J : Disorder N p, ∀ x : ℝ,
      HasDerivAt (fun y => hamiltonianCoefficient I (X (Function.update J I y,ω)))
        (dF I (Function.update J I x,ω)) x)
    (hf : ∀ I : TensorIndex N p,
      Integrable (fun z => hamiltonianCoefficient I (X z)) ((disorderLaw N p).prod ν))
    (hdf : ∀ I : TensorIndex N p, Integrable (dF I) ((disorderLaw N p).prod ν))
    (hIF : ∀ I : TensorIndex N p,
      Integrable (fun z : Disorder N p × Ω => z.1 I*hamiltonianCoefficient I (X z))
        ((disorderLaw N p).prod ν)) :
    Integrable (fun z : Disorder N p × Ω => Hamiltonian N p z.1 (X z)) ((disorderLaw N p).prod ν) ∧
      (∫ z : Disorder N p × Ω, Hamiltonian N p z.1 (X z) ∂(disorderLaw N p).prod ν)=
        ∑ I : TensorIndex N p, ∫ z : Disorder N p × Ω, dF I z ∂(disorderLaw N p).prod ν := by
  have hi : Integrable (fun z : Disorder N p × Ω =>
      ∑ I : TensorIndex N p, z.1 I*hamiltonianCoefficient I (X z)) ((disorderLaw N p).prod ν) :=
    integrable_finsetSum Finset.univ (fun I _ => hIF I)
  refine ⟨?_,?_⟩
  · simpa only [hamiltonian_eq_sum_coefficients] using hi
  · simp_rw [hamiltonian_eq_sum_coefficients]
    rw [integral_finsetSum _ (fun I _ => hIF I)]
    apply Finset.sum_congr rfl
    intro I _
    exact disorder_integration_by_parts_with_randomness ν I (hd I) (hf I) (hdf I) (hIF I)

end SphericalAging.GaussianIntegrationByParts
