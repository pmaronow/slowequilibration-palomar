module

public import SphericalAging.JointLpRepresentative
public import Mathlib.MeasureTheory.Function.L2Space

public section

set_option backward.privateInPublic true

/-! Constructive scalar L² Fubini isometry. The jointly measurable
representative is constructed from the actual L² family, and norm/linearity
are proved from the true slice classes and product measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ScalarFamilyLift
set_option maxHeartbeats 1800000
variable {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
  {ρ : Measure A} {μ : Measure B} [SFinite ρ] [SFinite μ]

private def familyVersion (f : Lp (Lp ℝ 2 μ) 2 ρ) : A × B → ℝ :=
  (JointLpRepresentative.exists_joint_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose

omit [SFinite ρ] [SFinite μ] in
private lemma familyVersion_sm (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    StronglyMeasurable[mA.prod mB] (familyVersion f) :=
  (JointLpRepresentative.exists_joint_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose_spec.1

omit [SFinite ρ] [SFinite μ] in
private lemma familyVersion_ae (f : Lp (Lp ℝ 2 μ) 2 ρ) (a : A) :
    (fun z => familyVersion f (a,z)) =ᵐ[μ]
      (f a : Lp ℝ 2 μ) :=
  (JointLpRepresentative.exists_joint_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose_spec.2 a

private lemma familyVersion_ambient (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    StronglyMeasurable (familyVersion f) := familyVersion_sm f

/-- The true L² norm formula for an actual Hilbert-valued quotient class. -/
lemma integral_norm_sq_Lp {B E : Type*} [MeasurableSpace B] {μ : Measure B}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Lp E 2 μ) :
    ∫ z, ‖f z‖^2 ∂μ = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun z => (real_inner_self_eq_norm_sq (f z)).symm)

private lemma slice_memLp (f : Lp (Lp ℝ 2 μ) 2 ρ) (a : A) :
    MemLp (fun z => familyVersion f (a,z)) 2 (μ) :=
  (Lp.memLp (f a : Lp ℝ 2 μ)).ae_eq (familyVersion_ae f a).symm

private lemma slice_integral_sq (f : Lp (Lp ℝ 2 μ) 2 ρ) (a : A) :
    ∫ z, familyVersion f (a,z)^2 ∂μ = ‖f a‖^2 := by
  have he : ∫ z, familyVersion f (a,z)^2 ∂μ =
      ∫ z, (f a : Lp ℝ 2 μ) z^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [familyVersion_ae f a] with z hz
    exact congrArg (fun x : ℝ => x^2) hz
  calc
    _ = ∫ z, (f a : Lp ℝ 2 μ) z^2 ∂μ := he
    _ = ‖f a‖^2 := by simpa only [Real.norm_eq_abs,sq_abs] using integral_norm_sq_Lp (f a : Lp ℝ 2 μ)

private lemma familyVersion_memLp (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    MemLp (familyVersion f) 2 (ρ.prod (μ)) := by
  apply (memLp_two_iff_integrable_sq (familyVersion_ambient f).aestronglyMeasurable).mpr
  apply (integrable_prod_iff ((familyVersion_ambient f).pow 2).aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun a => (slice_memLp f a).integrable_sq),?_⟩
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  simpa only [Pi.pow_apply,Real.norm_of_nonneg (sq_nonneg _),slice_integral_sq] using hi

/-- Actual joint random-variable class of a square-integrable L² family. -/
@[expose] def familyLift (f : Lp (Lp ℝ 2 μ) 2 ρ) : Lp ℝ 2 (ρ.prod μ) :=
  (familyVersion_memLp f).toLp (familyVersion f)

lemma familyLift_coe (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    familyLift f =ᵐ[ρ.prod μ] familyVersion f := MemLp.coeFn_toLp _

/-- Actual Fubini isometry of scalar family classes. -/
theorem familyLift_norm (f : Lp (Lp ℝ 2 μ) 2 ρ) : ‖familyLift f‖=‖f‖ := by
  have hn : ‖familyLift f‖^2=‖f‖^2 := by
    calc
      _ = ∫ z, ‖familyLift f z‖^2 ∂ρ.prod μ := (integral_norm_sq_Lp _).symm
      _ = ∫ z, (familyVersion f z)^2 ∂ρ.prod μ := by
        apply integral_congr_ae
        filter_upwards [familyLift_coe f] with z hz
        simp only [hz,Real.norm_eq_abs,sq_abs]
      _ = ∫ a, ∫ z, (familyVersion f (a,z))^2 ∂μ ∂ρ :=
        integral_prod _ (familyVersion_memLp f).integrable_sq
      _ = ∫ a, ‖f a‖^2 ∂ρ := by simp only [slice_integral_sq]
      _ = ‖f‖^2 := integral_norm_sq_Lp f
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

private lemma familyVersion_add_ae (f g : Lp (Lp ℝ 2 μ) 2 ρ) :
    familyVersion (f+g) =ᵐ[ρ.prod (μ)]
      (fun z => familyVersion f z+familyVersion g z) := by
  apply (Measure.ae_prod_iff_ae_ae ((familyVersion_ambient (f+g)).measurableSet_eq_fun
    ((familyVersion_ambient f).add (familyVersion_ambient g)))).mpr
  filter_upwards [Lp.coeFn_add f g] with a ha
  change (f+g) a=f a+g a at ha
  filter_upwards [familyVersion_ae (f+g) a,familyVersion_ae f a,familyVersion_ae g a,
    Lp.coeFn_add (f a : Lp ℝ 2 μ) (g a : Lp ℝ 2 μ)] with z hfg hf hg hs
  rw [hfg,ha]
  change ((f a : Lp ℝ 2 μ)+(g a : Lp ℝ 2 μ)) z=familyVersion f (a,z)+familyVersion g (a,z)
  rw [hs,Pi.add_apply,hf,hg]

lemma familyLift_add (f g : Lp (Lp ℝ 2 μ) 2 ρ) :
    familyLift (f+g)=familyLift f+familyLift g := by
  apply Lp.ext
  have he := familyVersion_add_ae f g
  filter_upwards [familyLift_coe (f+g),familyLift_coe f,familyLift_coe g,he,
    Lp.coeFn_add (familyLift f : Lp ℝ 2 (ρ.prod μ)) (familyLift g : Lp ℝ 2 (ρ.prod μ))]
    with z hfg hf hg he hs
  change (familyLift (f+g) : Lp ℝ 2 (ρ.prod μ)) z=
    ((familyLift f : Lp ℝ 2 (ρ.prod μ))+(familyLift g : Lp ℝ 2 (ρ.prod μ))) z
  rw [hfg,hs,Pi.add_apply,hf,hg,he]

private lemma familyVersion_smul_ae (c : ℝ) (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    familyVersion (c • f) =ᵐ[ρ.prod (μ)]
      (fun z => c*familyVersion f z) := by
  apply (Measure.ae_prod_iff_ae_ae ((familyVersion_ambient (c • f)).measurableSet_eq_fun
    (stronglyMeasurable_const.mul (familyVersion_ambient f)))).mpr
  filter_upwards [Lp.coeFn_smul c f] with a ha
  change (c • f) a=c • f a at ha
  filter_upwards [familyVersion_ae (c • f) a,familyVersion_ae f a,
    Lp.coeFn_smul c (f a : Lp ℝ 2 μ)] with z hcf hf hs
  rw [hcf,ha]
  change (c • (f a : Lp ℝ 2 μ)) z=c*familyVersion f (a,z)
  rw [hs,Pi.smul_apply,smul_eq_mul,hf]

lemma familyLift_smul (c : ℝ) (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    familyLift (c • f)=c • familyLift f := by
  apply Lp.ext
  have he := familyVersion_smul_ae c f
  filter_upwards [familyLift_coe (c • f),familyLift_coe f,he,
    Lp.coeFn_smul c (familyLift f : Lp ℝ 2 (ρ.prod μ))] with z hcf hf he hs
  change (familyLift (c • f) : Lp ℝ 2 (ρ.prod μ)) z=(c • (familyLift f : Lp ℝ 2 (ρ.prod μ))) z
  rw [hcf,hs,Pi.smul_apply,smul_eq_mul,hf,he]

/-- Actual isometric linear Fubini embedding. -/
@[expose] def familyLiftLI : Lp (Lp ℝ 2 μ) 2 ρ →ₗᵢ[ℝ] Lp ℝ 2 (ρ.prod μ) where
  toFun := familyLift
  map_add' := familyLift_add
  map_smul' := familyLift_smul
  norm_map' := familyLift_norm

/-- Almost every parameter slice is the actual input L² class. -/
theorem familyLift_slice_ae (f : Lp (Lp ℝ 2 μ) 2 ρ) :
    ∀ᵐ a ∂ρ, (fun z => familyLift f (a,z)) =ᵐ[μ] (f a : Lp ℝ 2 μ) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (familyLift_coe f)] with a ha
  exact Filter.EventuallyEq.trans ha (familyVersion_ae f a)

/-- Identify an actual joint scalar L² class by its genuine parameter
slices. -/
theorem familyLift_eq_of_slices (f : Lp (Lp ℝ 2 μ) 2 ρ) (V : Lp ℝ 2 (ρ.prod μ))
    (hV : ∀ᵐ a ∂ρ, (fun z => V (a,z)) =ᵐ[μ] (f a : Lp ℝ 2 μ)) : familyLift f=V := by
  have he : V =ᵐ[ρ.prod μ] familyVersion f := by
    apply (Measure.ae_prod_iff_ae_ae ((Lp.stronglyMeasurable V).measurableSet_eq_fun (familyVersion_ambient f))).mpr
    filter_upwards [hV] with a ha
    exact Filter.EventuallyEq.trans ha (Filter.EventuallyEq.symm (familyVersion_ae f a))
  exact Lp.ext ((familyLift_coe f).trans he.symm)

end SphericalAging.ScalarFamilyLift
