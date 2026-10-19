module

public import SphericalAging.BackgroundItoLift
public import SphericalAging.JointPredictableRepresentative

public section

set_option backward.privateInPublic true

/-! Actual Fubini lift of square-integrable parameter families of predictable
L² classes into the enlarged predictable space. Joint representatives are
constructed; linearity and the norm identity follow from Fubini and the
actual slice classes, not from an assumed stochastic Fubini property.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PredictableFamilyLift
open HardSphereDynamics IndependentBackgroundDriver BackgroundItoLift
open JointPredictableRepresentative
set_option maxHeartbeats 1800000
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

/-- Reorder the actual parameter/time/sample coordinates. -/
@[expose] def shuffle (z : ℝ≥0 × (A × Ω)) : A × (ℝ≥0 × Ω) := (z.2.1,(z.1,z.2.2))

lemma shuffle_measurePreserving : MeasurePreserving (shuffle : ℝ≥0 × (A × Ω) → A × (ℝ≥0 × Ω))
    (nonnegativeLebesgueMeasure.prod (ρ.prod P)) (ρ.prod (nonnegativeLebesgueMeasure.prod P)) := by
  have hi := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc nonnegativeLebesgueMeasure ρ P)
  have hs : MeasurePreserving (Prod.swap : ℝ≥0 × A → A × ℝ≥0)
      (nonnegativeLebesgueMeasure.prod ρ) (ρ.prod nonnegativeLebesgueMeasure) := Measure.measurePreserving_swap
  have hp := hs.prod (MeasurePreserving.id P)
  exact (measurePreserving_prodAssoc ρ nonnegativeLebesgueMeasure P).comp (hp.comp hi)

lemma shuffle_measurableEmbedding : MeasurableEmbedding (shuffle : ℝ≥0 × (A × Ω) → A × (ℝ≥0 × Ω)) := by
  let e : (ℝ≥0 × (A × Ω)) ≃ᵐ (A × (ℝ≥0 × Ω)) :=
    ((MeasurableEquiv.prodAssoc : (ℝ≥0 × A) × Ω ≃ᵐ ℝ≥0 × (A × Ω)).symm.trans
      ((MeasurableEquiv.prodComm : ℝ≥0 × A ≃ᵐ A × ℝ≥0).prodCongr (MeasurableEquiv.refl Ω))).trans
        MeasurableEquiv.prodAssoc
  exact e.measurableEmbedding

lemma parameter_predictable : @Measurable (ℝ≥0 × (A × Ω)) A (filtration A F).predictable mA
    (fun z => z.2.1) := by
  intro S hS
  have hE : MeasurableSet[filtration A F 0] (S ×ˢ (univ : Set Ω)) := hS.prod MeasurableSet.univ
  have h0 := measurableSet_predictable_singleton_bot_prod (𝓕 := filtration A F) hE
  have h1 := measurableSet_predictable_Ioi_prod (𝓕 := filtration A F) (i := 0) hE
  convert h0.union h1 using 1
  ext z
  simp only [mem_preimage,mem_union,mem_prod,mem_singleton_iff,mem_univ,and_true,mem_Ioi]
  constructor
  · intro hz
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ z.1) with ht|ht
    · exact Or.inl ⟨ht.symm,hz⟩
    · exact Or.inr ⟨ht,hz⟩
  · rintro (⟨_,hz⟩|⟨_,hz⟩)
    exact hz
    exact hz

lemma shuffle_predictable : @Measurable (ℝ≥0 × (A × Ω)) (A × (ℝ≥0 × Ω))
    (filtration A F).predictable (mA.prod F.predictable) shuffle :=
  parameter_predictable.prodMk timeProjection_predictable

private def familyVersion (f : Lp (PredictableProcessL2 F P) 2 ρ) : A × (ℝ≥0 × Ω) → ℝ :=
  (exists_joint_predictable_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose

omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure P] in
private lemma familyVersion_sm (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    StronglyMeasurable[mA.prod F.predictable] (familyVersion f) :=
  (exists_joint_predictable_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose_spec.1

omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure P] in
private lemma familyVersion_ae (f : Lp (PredictableProcessL2 F P) 2 ρ) (a : A) :
    (fun z => familyVersion f (a,z)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (f a : TimeProcessL2 P) :=
  (exists_joint_predictable_representative (fun a => f a) (Lp.stronglyMeasurable f)).choose_spec.2 a

private lemma familyVersion_ambient (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    StronglyMeasurable (familyVersion f) :=
  (familyVersion_sm f).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (predictable_le_prod F)))

/-- The true L² norm formula for an actual Hilbert-valued quotient class. -/
lemma integral_norm_sq_Lp {B E : Type*} [MeasurableSpace B] {μ : Measure B}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : Lp E 2 μ) :
    ∫ z, ‖f z‖^2 ∂μ = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun z => (real_inner_self_eq_norm_sq (f z)).symm)

private lemma slice_memLp (f : Lp (PredictableProcessL2 F P) 2 ρ) (a : A) :
    MemLp (fun z => familyVersion f (a,z)) 2 (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp (f a : TimeProcessL2 P)).ae_eq (familyVersion_ae f a).symm

private lemma slice_integral_sq (f : Lp (PredictableProcessL2 F P) 2 ρ) (a : A) :
    ∫ z, familyVersion f (a,z)^2 ∂nonnegativeLebesgueMeasure.prod P = ‖f a‖^2 := by
  have he : ∫ z, familyVersion f (a,z)^2 ∂nonnegativeLebesgueMeasure.prod P =
      ∫ z, (f a : TimeProcessL2 P) z^2 ∂nonnegativeLebesgueMeasure.prod P := by
    apply integral_congr_ae
    filter_upwards [familyVersion_ae f a] with z hz
    exact congrArg (fun x : ℝ => x^2) hz
  calc
    _ = ∫ z, (f a : TimeProcessL2 P) z^2 ∂nonnegativeLebesgueMeasure.prod P := he
    _ = ‖f a‖^2 := by
      change _ = ‖(f a : TimeProcessL2 P)‖^2
      simpa only [Real.norm_eq_abs,sq_abs] using integral_norm_sq_Lp (f a : TimeProcessL2 P)

private lemma familyVersion_memLp (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    MemLp (familyVersion f) 2 (ρ.prod (nonnegativeLebesgueMeasure.prod P)) := by
  apply (memLp_two_iff_integrable_sq (familyVersion_ambient f).aestronglyMeasurable).mpr
  apply (integrable_prod_iff ((familyVersion_ambient f).pow 2).aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun a => (slice_memLp f a).integrable_sq),?_⟩
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  simpa only [Pi.pow_apply,Real.norm_of_nonneg (sq_nonneg _),slice_integral_sq] using hi

/-- Genuine enlarged-filtration predictable L² class of the actual family. -/
@[expose] def familyLift (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    PredictableProcessL2 (filtration A F) (ρ.prod P) := by
  let G := fun z => familyVersion f (shuffle z)
  have hG : StronglyMeasurable[(filtration A F).predictable] G :=
    (familyVersion_sm f).comp_measurable shuffle_predictable
  have hm : MemLp G 2 (nonnegativeLebesgueMeasure.prod (ρ.prod P)) :=
    (familyVersion_memLp f).comp_measurePreserving shuffle_measurePreserving
  exact ⟨hm.toLp G,hG.aestronglyMeasurable.congr hm.coeFn_toLp.symm⟩

lemma familyLift_coe (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    (familyLift f : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      (fun z => familyVersion f (shuffle z)) :=
  ((familyVersion_memLp f).comp_measurePreserving (shuffle_measurePreserving (ρ := ρ) (P := P))).coeFn_toLp

/-- Actual Fubini isometry of predictable family classes. -/
theorem familyLift_norm (f : Lp (PredictableProcessL2 F P) 2 ρ) : ‖familyLift f‖=‖f‖ := by
  have hn : ‖familyLift f‖^2=‖f‖^2 := by
    calc
      _ = ∫ z, ‖(familyLift f : TimeProcessL2 (ρ.prod P)) z‖^2
          ∂nonnegativeLebesgueMeasure.prod (ρ.prod P) := (integral_norm_sq_Lp _).symm
      _ = ∫ z, (familyVersion f (shuffle z))^2 ∂nonnegativeLebesgueMeasure.prod (ρ.prod P) := by
        apply integral_congr_ae
        filter_upwards [familyLift_coe f] with z hz
        simp only [hz,Real.norm_eq_abs,sq_abs]
      _ = ∫ z, (familyVersion f z)^2 ∂ρ.prod (nonnegativeLebesgueMeasure.prod P) :=
        (shuffle_measurePreserving (ρ := ρ) (P := P)).integral_comp shuffle_measurableEmbedding
          (fun z : A × (ℝ≥0 × Ω) => familyVersion f z^2)
      _ = ∫ a, ∫ z, (familyVersion f (a,z))^2 ∂nonnegativeLebesgueMeasure.prod P ∂ρ :=
        integral_prod _ (familyVersion_memLp f).integrable_sq
      _ = ∫ a, ‖f a‖^2 ∂ρ := by simp only [slice_integral_sq]
      _ = ‖f‖^2 := integral_norm_sq_Lp f
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

private lemma familyVersion_add_ae (f g : Lp (PredictableProcessL2 F P) 2 ρ) :
    familyVersion (f+g) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      (fun z => familyVersion f z+familyVersion g z) := by
  apply (Measure.ae_prod_iff_ae_ae ((familyVersion_ambient (f+g)).measurableSet_eq_fun
    ((familyVersion_ambient f).add (familyVersion_ambient g)))).mpr
  filter_upwards [Lp.coeFn_add f g] with a ha
  change (f+g) a=f a+g a at ha
  filter_upwards [familyVersion_ae (f+g) a,familyVersion_ae f a,familyVersion_ae g a,
    Lp.coeFn_add (f a : TimeProcessL2 P) (g a : TimeProcessL2 P)] with z hfg hf hg hs
  rw [hfg,ha]
  change ((f a : TimeProcessL2 P)+(g a : TimeProcessL2 P)) z=familyVersion f (a,z)+familyVersion g (a,z)
  rw [hs,Pi.add_apply,hf,hg]

lemma familyLift_add (f g : Lp (PredictableProcessL2 F P) 2 ρ) :
    familyLift (f+g)=familyLift f+familyLift g := by
  apply Subtype.ext
  apply Lp.ext
  have he := (shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (familyVersion_add_ae f g)
  filter_upwards [familyLift_coe (f+g),familyLift_coe f,familyLift_coe g,he,
    Lp.coeFn_add (familyLift f : TimeProcessL2 (ρ.prod P)) (familyLift g : TimeProcessL2 (ρ.prod P))]
    with z hfg hf hg he hs
  dsimp only [Function.comp_def] at he
  change (familyLift (f+g) : TimeProcessL2 (ρ.prod P)) z=
    ((familyLift f : TimeProcessL2 (ρ.prod P))+(familyLift g : TimeProcessL2 (ρ.prod P))) z
  rw [hfg,hs,Pi.add_apply,hf,hg,he]

private lemma familyVersion_smul_ae (c : ℝ) (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    familyVersion (c • f) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      (fun z => c*familyVersion f z) := by
  apply (Measure.ae_prod_iff_ae_ae ((familyVersion_ambient (c • f)).measurableSet_eq_fun
    (stronglyMeasurable_const.mul (familyVersion_ambient f)))).mpr
  filter_upwards [Lp.coeFn_smul c f] with a ha
  change (c • f) a=c • f a at ha
  filter_upwards [familyVersion_ae (c • f) a,familyVersion_ae f a,
    Lp.coeFn_smul c (f a : TimeProcessL2 P)] with z hcf hf hs
  rw [hcf,ha]
  change (c • (f a : TimeProcessL2 P)) z=c*familyVersion f (a,z)
  rw [hs,Pi.smul_apply,smul_eq_mul,hf]

lemma familyLift_smul (c : ℝ) (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    familyLift (c • f)=c • familyLift f := by
  apply Subtype.ext
  apply Lp.ext
  have he := (shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (familyVersion_smul_ae c f)
  filter_upwards [familyLift_coe (c • f),familyLift_coe f,he,
    Lp.coeFn_smul c (familyLift f : TimeProcessL2 (ρ.prod P))] with z hcf hf he hs
  dsimp only [Function.comp_def] at he
  change (familyLift (c • f) : TimeProcessL2 (ρ.prod P)) z=(c • (familyLift f : TimeProcessL2 (ρ.prod P))) z
  rw [hcf,hs,Pi.smul_apply,smul_eq_mul,hf,he]

/-- The actual isometric linear Fubini embedding into the enlarged
predictable space. -/
@[expose] def familyLiftLI : Lp (PredictableProcessL2 F P) 2 ρ →ₗᵢ[ℝ]
    PredictableProcessL2 (filtration A F) (ρ.prod P) where
  toFun := familyLift
  map_add' := familyLift_add
  map_smul' := familyLift_smul
  norm_map' := familyLift_norm

/-- Identify an actual enlarged predictable class by its genuine parameter
slices. This is plain L² uniqueness under product almost-everywhere equality. -/
theorem familyLift_eq_of_slices (f : Lp (PredictableProcessL2 F P) 2 ρ)
    (V : PredictableProcessL2 (filtration A F) (ρ.prod P))
    (hV : ∀ᵐ a ∂ρ, (fun z : ℝ≥0 × Ω => (V : TimeProcessL2 (ρ.prod P)) (z.1,(a,z.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (f a : TimeProcessL2 P)) : familyLift f=V := by
  have hsm : StronglyMeasurable (fun q : A × (ℝ≥0 × Ω) =>
      (V : TimeProcessL2 (ρ.prod P)) (q.2.1,(q.1,q.2.2))) :=
    (Lp.stronglyMeasurable (V : TimeProcessL2 (ρ.prod P))).comp_measurable
      (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
  have he : (fun q : A × (ℝ≥0 × Ω) => (V : TimeProcessL2 (ρ.prod P)) (q.2.1,(q.1,q.2.2)))
      =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)] familyVersion f := by
    apply (Measure.ae_prod_iff_ae_ae (hsm.measurableSet_eq_fun (familyVersion_ambient f))).mpr
    filter_upwards [hV] with a ha
    exact Filter.EventuallyEq.trans ha (Filter.EventuallyEq.symm (familyVersion_ae f a))
  have hb := (shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp he
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [familyLift_coe f,hb] with z hG hV
  dsimp only [Function.comp_def,shuffle] at hV
  exact hG.trans hV.symm

end SphericalAging.PredictableFamilyLift
