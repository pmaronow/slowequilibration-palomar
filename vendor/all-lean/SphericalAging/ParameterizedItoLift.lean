module

public import SphericalAging.PredictableFamilyLift
public import SphericalAging.ScalarFamilyLift
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

public section

/-! Stochastic Fubini for actual independent-background parameter families.
The identity is established for parameter indicators and elementary time
integrands, then extended twice by the genuine L² density theorems.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ParameterizedItoLift
local instance : (q : Prop) → Decidable q := Classical.propDecidable
open HardSphereDynamics VectorIto IndependentBackgroundDriver BackgroundItoLift
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 2000000
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℕ}

/-- Actual inverse coordinate permutation for taking parameter sections. -/
@[expose] def unshuffle (z : A × (ℝ≥0 × Ω)) : ℝ≥0 × (A × Ω) := (z.2.1,(z.1,z.2.2))

lemma unshuffle_measurePreserving : MeasurePreserving (unshuffle : A × (ℝ≥0 × Ω) → ℝ≥0 × (A × Ω))
    (ρ.prod (nonnegativeLebesgueMeasure.prod P)) (nonnegativeLebesgueMeasure.prod (ρ.prod P)) := by
  have hi := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ρ nonnegativeLebesgueMeasure P)
  have hs : MeasurePreserving (Prod.swap : A × ℝ≥0 → ℝ≥0 × A)
      (ρ.prod nonnegativeLebesgueMeasure) (nonnegativeLebesgueMeasure.prod ρ) := Measure.measurePreserving_swap
  have hp := hs.prod (MeasurePreserving.id P)
  exact (measurePreserving_prodAssoc nonnegativeLebesgueMeasure ρ P).comp (hp.comp hi)

/-- Parameterwise application of the actual full-filtration Itô CLM. -/
@[expose] def fibreIto (D : BrownianDriver N P F) (i : Fin N) :
    Lp (PredictableProcessL2 F P) 2 ρ →L[ℝ] Lp (RandomL2 P) 2 ρ :=
  (coordinateIto D i).compLpL 2 ρ

lemma fibreIto_coe (D : BrownianDriver N P F) (i : Fin N)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    fibreIto D i f =ᵐ[ρ] (fun a => coordinateIto D i (f a)) :=
  (coordinateIto D i).coeFn_compLp f

/-- The genuine adapted coefficient of a parameter indicator times a
base F_s-measurable random variable. -/
@[expose] def adaptedIndicator (S : Set A) (hS : MeasurableSet S) (s : ℝ≥0)
    (Z : lpMeas ℝ ℝ (F s) 2 P) : lpMeas ℝ ℝ (filtration A F s) 2 (ρ.prod P) := by
  let hZ := lpMeas.aestronglyMeasurable Z
  let G := (S ×ˢ (univ : Set Ω)).indicator (fun q : A × Ω => hZ.mk (Z : RandomL2 P) q.2)
  have hG : StronglyMeasurable[filtration A F s] G :=
    (hZ.stronglyMeasurable_mk.comp_measurable (base_known s)).indicator (hS.prod MeasurableSet.univ)
  have hm : MemLp G 2 (ρ.prod P) :=
    (((Lp.memLp (Z : RandomL2 P)).ae_eq hZ.ae_eq_mk).comp_measurePreserving
      (measurePreserving_snd (μ := ρ) (ν := P))).indicator (hS.prod MeasurableSet.univ)
  exact ⟨hm.toLp G,hG.aestronglyMeasurable.congr hm.coeFn_toLp.symm⟩

lemma adaptedIndicator_coe (S : Set A) (hS : MeasurableSet S) (s : ℝ≥0)
    (Z : lpMeas ℝ ℝ (F s) 2 P) :
    (adaptedIndicator (ρ := ρ) S hS s Z : RandomL2 (ρ.prod P)) =ᵐ[ρ.prod P]
      (fun q : A × Ω => if q.1 ∈ S then (Z : RandomL2 P) q.2 else 0) := by
  let hZ := lpMeas.aestronglyMeasurable Z
  have hm : MemLp ((S ×ˢ (univ : Set Ω)).indicator (fun q : A × Ω => hZ.mk (Z : RandomL2 P) q.2))
      2 (ρ.prod P) :=
    (((Lp.memLp (Z : RandomL2 P)).ae_eq hZ.ae_eq_mk).comp_measurePreserving
      (measurePreserving_snd (μ := ρ) (ν := P))).indicator (hS.prod MeasurableSet.univ)
  have hz := (measurePreserving_snd (μ := ρ) (ν := P)).quasiMeasurePreserving.ae_eq_comp hZ.ae_eq_mk
  filter_upwards [hm.coeFn_toLp,hz] with q hG hZ
  change (((hm.toLp _) : RandomL2 (ρ.prod P)) : A × Ω → ℝ) q=_
  rw [hG]
  dsimp only [Function.comp_def] at hZ
  by_cases h : q.1 ∈ S
  · simp [h,hZ]
  · simp [h]

lemma predictableFamily_indicator_elementary (S : Set A) (hS : MeasurableSet S) (hρS : ρ S ≠ ∞)
    {s t : ℝ≥0} (Z : lpMeas ℝ ℝ (F s) 2 P) :
    PredictableFamilyLift.familyLift (indicatorConstLp 2 hS hρS (elementaryPredictable F s t Z)) =
      elementaryPredictable (filtration A F) s t (adaptedIndicator S hS s Z) := by
  apply PredictableFamilyLift.familyLift_eq_of_slices
  have hv := (unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (elementaryPredictable_coeFn (filtration A F) s t (adaptedIndicator (ρ := ρ) S hS s Z))
  have hz := Measure.ae_ae_of_ae_prod (adaptedIndicator_coe (ρ := ρ) S hS s Z)
  filter_upwards [Measure.ae_ae_of_ae_prod hv,hz,indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hρS)
    (c := elementaryPredictable F s t Z)] with a hv hz ha
  have hzt := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hz
  by_cases haS : a ∈ S
  · simp only [indicator_of_mem haS] at ha
    rw [ha]
    filter_upwards [hv,hzt,elementaryPredictable_coeFn F s t Z] with z hv hz hu
    dsimp only [Function.comp_def,unshuffle] at hv
    simp only [ite_eq_left haS] at hz
    rw [hv,hu]
    simp only [hz]
    rfl
  · simp only [indicator_of_notMem haS] at ha
    rw [ha]
    filter_upwards [hv,hzt,Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with z hv hz hu
    dsimp only [Function.comp_def,unshuffle] at hv
    simp only [ite_eq_right haS] at hz
    change _ = ((0 : TimeProcessL2 P) : ℝ≥0 × Ω → ℝ) z
    rw [hv,hu]
    simp [hz]

lemma coordinateIto_indicator_elementary (D : BrownianDriver N P F) (i : Fin N)
    (S : Set A) (hS : MeasurableSet S) (hρS : ρ S ≠ ∞)
    {s t : ℝ≥0} (hst : s ≤ t) (Z : lpMeas ℝ ℝ (F s) 2 P) :
    coordinateIto (driver (ρ := ρ) D) i
      (PredictableFamilyLift.familyLift (indicatorConstLp 2 hS hρS (elementaryPredictable F s t Z))) =
    ScalarFamilyLift.familyLift (fibreIto D i (indicatorConstLp 2 hS hρS (elementaryPredictable F s t Z))) := by
  rw [predictableFamily_indicator_elementary]
  apply Eq.symm
  apply ScalarFamilyLift.familyLift_eq_of_slices
  have hv := Measure.ae_ae_of_ae_prod (coeFn_elementaryBrownianValue
    ((driver (ρ := ρ) D).filtered i).toIsPreBrownianReal
    ((driver (ρ := ρ) D).coordinateStronglyMeasurable i) ((driver (ρ := ρ) D).filtered i) hst
    (adaptedIndicator (ρ := ρ) S hS s Z))
  have hz := Measure.ae_ae_of_ae_prod (adaptedIndicator_coe (ρ := ρ) S hS s Z)
  filter_upwards [hv,hz,fibreIto_coe D i (indicatorConstLp 2 hS hρS (elementaryPredictable F s t Z)),
    indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hρS) (c := elementaryPredictable F s t Z)]
    with a hv hz hI ha
  rw [hI]
  unfold coordinateIto
  rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst)]
  by_cases haS : a ∈ S
  · simp only [indicator_of_mem haS] at ha
    rw [ha]
    rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst)]
    filter_upwards [hv,hz,coeFn_elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z] with ω hv hz hu
    rw [hv,hu]
    simp only [ite_eq_left haS] at hz
    rw [hz]
    rfl
  · simp only [indicator_of_notMem haS] at ha
    rw [ha,map_zero]
    filter_upwards [hv,hz,Lp.coeFn_zero ℝ 2 P] with ω hv hz hu
    rw [hv,hu]
    simp only [ite_eq_right haS] at hz
    simp [hz]

/-- The actual outer-parameter indicator embedding is a bounded linear
map, so elementary time-integrand density applies to parameter indicators. -/
@[expose] def indicatorFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set A) (hS : MeasurableSet S) (hρS : ρ S ≠ ∞) : E →L[ℝ] Lp E 2 ρ := by
  let L : E →ₗ[ℝ] Lp E 2 ρ :=
    { toFun := indicatorConstLp 2 hS hρS
      map_add' := fun x y => indicatorConstLp_add.symm
      map_smul' := by
        intro c x
        change indicatorConstLp 2 hS hρS (c • x) = c • indicatorConstLp 2 hS hρS x
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hρS) (c := c • x),
          indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hρS) (c := x),
          Lp.coeFn_smul c (indicatorConstLp 2 hS hρS x)] with a hx hy hz
        rw [hx,hz]
        simp only [Pi.smul_apply,hy]
        by_cases ha : a ∈ S
        · simp [ha]
        · simp [ha] }
  exact L.mkContinuous (ρ.real S ^ (1 / (2 : ℝ≥0∞).toReal))
    (fun x => (norm_indicatorConstLp_le (p := 2) (hs := hS) (hμs := hρS) (c := x)).trans_eq (mul_comm _ _))

lemma indicatorFamily_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set A) (hS : MeasurableSet S) (hρS : ρ S ≠ ∞) (x : E) :
    indicatorFamily S hS hρS x = indicatorConstLp 2 hS hρS x := rfl

/-- First density extension: an arbitrary base predictable L² integrand
multiplied by an actual finite-measure parameter indicator. -/
theorem coordinateIto_indicator (D : BrownianDriver N P F) (i : Fin N)
    (S : Set A) (hS : MeasurableSet S) (hρS : ρ S ≠ ∞)
    (U : PredictableProcessL2 F P) :
    coordinateIto (driver (ρ := ρ) D) i
      (PredictableFamilyLift.familyLift (indicatorConstLp 2 hS hρS U)) =
    ScalarFamilyLift.familyLift (fibreIto D i (indicatorConstLp 2 hS hρS U)) := by
  let L := ((coordinateIto (driver (ρ := ρ) D) i).comp
    PredictableFamilyLift.familyLiftLI.toContinuousLinearMap).comp (indicatorFamily S hS hρS)
  let R := ((ScalarFamilyLift.familyLiftLI (ρ := ρ) (μ := P)).toContinuousLinearMap.comp (fibreIto D i)).comp
    (indicatorFamily S hS hρS)
  change L U = R U
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P) F).induction_on U
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have he (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex F P) :
      L (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x) = R (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x) :=
    coordinateIto_indicator_elementary D i S hS hρS x.2.1.2 x.2.2
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable F P v =
      ∑ x ∈ v.support, v x • FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,Finsupp.linearCombination_apply,Finsupp.sum]
  rw [hv,map_sum,map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun Y => v x • Y) (he x))

/-- Actual stochastic Fubini on the independent enlarged filtration.
No random-parameter Itô equality is assumed: both density extensions use
the concrete elementary Brownian-increment integral. -/
theorem coordinateIto_familyLift (D : BrownianDriver N P F) (i : Fin N)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    coordinateIto (driver (ρ := ρ) D) i (PredictableFamilyLift.familyLift f) =
      ScalarFamilyLift.familyLift (fibreIto D i f) := by
  let L := (coordinateIto (driver (ρ := ρ) D) i).comp
    PredictableFamilyLift.familyLiftLI.toContinuousLinearMap
  let R := (ScalarFamilyLift.familyLiftLI (ρ := ρ) (μ := P)).toContinuousLinearMap.comp (fibreIto D i)
  change L f = R f
  refine Lp.induction (by norm_num) (fun f => L f = R f) ?_ ?_
    (isClosed_eq L.continuous R.continuous) f
  · intro U S hS hρS
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact coordinateIto_indicator D i S hS hρS.ne U
  · intro f g hf hg hdisjoint hfeq hgeq
    rw [map_add,map_add,hfeq,hgeq]

/-- Genuine parameter sections of the predictable Fubini class. -/
lemma predictableFamily_slice_ae (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    ∀ᵐ a ∂ρ, (fun z : ℝ≥0 × Ω =>
      (PredictableFamilyLift.familyLift f : TimeProcessL2 (ρ.prod P)) (z.1,(a,z.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (f a : TimeProcessL2 P) := by
  have he := (unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (PredictableFamilyLift.familyLift_coe f)
  filter_upwards [Measure.ae_ae_of_ae_prod he] with a ha
  let G := (JointPredictableRepresentative.exists_joint_predictable_representative
    (fun a => f a) (Lp.stronglyMeasurable f)).choose
  have heq : (fun z : ℝ≥0 × Ω =>
      (PredictableFamilyLift.familyLift f : TimeProcessL2 (ρ.prod P)) (z.1,(a,z.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun z => G (a,z)) := by
    filter_upwards [ha] with z hz
    exact hz
  exact Filter.EventuallyEq.trans heq ((JointPredictableRepresentative.exists_joint_predictable_representative
    (fun a => f a) (Lp.stronglyMeasurable f)).choose_spec.2 a)

/-- Deterministic time restriction commutes with the actual parameter
Fubini class, including the endpoint convention `(0,t]`. -/
theorem predictableTimeRestrict_familyLift (t : ℝ≥0)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict (filtration A F) t
      (PredictableFamilyLift.familyLift f) =
      PredictableFamilyLift.familyLift
        ((FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).compLpL 2 ρ f) := by
  apply Eq.symm
  apply PredictableFamilyLift.familyLift_eq_of_slices
  have hv := (unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn (filtration A F) t
      (PredictableFamilyLift.familyLift f))
  filter_upwards [Measure.ae_ae_of_ae_prod hv,predictableFamily_slice_ae f,
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).coeFn_compLp f]
    with a hv hu hfa
  change _ =ᵐ[nonnegativeLebesgueMeasure.prod P]
    (((FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t).compLp f) a : TimeProcessL2 P)
  rw [hfa]
  filter_upwards [hv,hu,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t (f a)]
    with z hv hu hcut
  dsimp only [Function.comp_def,unshuffle] at hv
  simp only [FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM_apply]
  rw [hv,hcut]
  simp only [FourPapersCommon.FilteredBrownian.predictableTimeFrame,Set.indicator,
    Set.mem_prod,Set.mem_univ,and_true,hu]

/-- The actual Itô terminal variable of a lifted parameter family has the
true deterministic-parameter Itô terminal variable as almost every slice. -/
theorem coordinateIto_familyLift_slice (D : BrownianDriver N P F) (i : Fin N)
    (f : Lp (PredictableProcessL2 F P) 2 ρ) :
    ∀ᵐ a ∂ρ, (fun ω => coordinateIto (driver (ρ := ρ) D) i
      (PredictableFamilyLift.familyLift f) (a,ω)) =ᵐ[P] (coordinateIto D i (f a) : RandomL2 P) := by
  rw [coordinateIto_familyLift]
  filter_upwards [ScalarFamilyLift.familyLift_slice_ae (fibreIto D i f),fibreIto_coe D i f] with a ha hfa
  simpa only [hfa] using ha

end SphericalAging.ParameterizedItoLift
