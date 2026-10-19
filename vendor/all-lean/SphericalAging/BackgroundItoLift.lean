module

public import SphericalAging.IndependentBackgroundDriver
public import SphericalAging.BoundedItoMultiplier

public section

/-! Actual Itô operators commute with independent-background pullback.
The operator identity is proved first on genuine elementary stochastic
integrals, then on all predictable L² integrands by the proved elementary
density theorem. This uses the enlarged product filtration, including the
full independent background at time zero.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.BackgroundItoLift
open HardSphereDynamics VectorIto IndependentBackgroundDriver
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
variable {A Ω : Type*} [mA : MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℕ}

/-- Discard only the independent background, retaining actual time and
Brownian sample coordinates. -/
@[expose] def timeProjection (z : ℝ≥0 × (A × Ω)) : ℝ≥0 × Ω := (z.1,z.2.2)

lemma timeProjection_measurePreserving :
    MeasurePreserving (timeProjection : ℝ≥0 × (A × Ω) → ℝ≥0 × Ω)
      (nonnegativeLebesgueMeasure.prod (ρ.prod P)) (nonnegativeLebesgueMeasure.prod P) :=
  (MeasurePreserving.id nonnegativeLebesgueMeasure).prod measurePreserving_snd

/-- Pulling back a genuinely predictable base integrand preserves the
actual enlarged predictable sigma algebra. -/
lemma timeProjection_predictable :
    @Measurable (ℝ≥0 × (A × Ω)) (ℝ≥0 × Ω) (filtration A F).predictable F.predictable timeProjection := by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro S hS
    change MeasurableSet[(filtration A F).predictable]
      ((timeProjection : ℝ≥0 × (A × Ω) → ℝ≥0 × Ω) ⁻¹' ({0} ×ˢ S))
    convert measurableSet_predictable_singleton_bot_prod (𝓕 := filtration A F) (MeasurableSet.univ.prod hS) using 1
    ext z
    simp [timeProjection]
  · intro t S hS
    change MeasurableSet[(filtration A F).predictable]
      ((timeProjection : ℝ≥0 × (A × Ω) → ℝ≥0 × Ω) ⁻¹' (Ioi t ×ˢ S))
    convert measurableSet_predictable_Ioi_prod (𝓕 := filtration A F) (MeasurableSet.univ.prod hS) using 1
    ext z
    simp [timeProjection]

/-- Actual ambient random-variable pullback as an isometric linear map. -/
@[expose] def randomLift : RandomL2 P →L[ℝ] RandomL2 (ρ.prod P) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (Prod.snd : A × Ω → Ω) measurePreserving_snd).toContinuousLinearMap

lemma randomLift_coe (Z : RandomL2 P) :
    (randomLift (ρ := ρ) Z : A × Ω → ℝ) =ᵐ[ρ.prod P] (fun q => Z q.2) :=
  Lp.coeFn_compMeasurePreserving Z measurePreserving_snd

/-- Actual ambient time/sample pullback as an isometric linear map. -/
@[expose] def timeLift : TimeProcessL2 P →L[ℝ] TimeProcessL2 (ρ.prod P) :=
  (Lp.compMeasurePreservingₗᵢ ℝ timeProjection timeProjection_measurePreserving).toContinuousLinearMap

lemma timeLift_coe (U : TimeProcessL2 P) :
    (timeLift (ρ := ρ) U : ℝ≥0 × (A × Ω) → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      (fun z => U (timeProjection z)) :=
  Lp.coeFn_compMeasurePreserving U timeProjection_measurePreserving

/-- Actual predictable pullback: membership is proved using a genuine
predictable representative and measure-preserving pullback. -/
@[expose] def predictableLift : PredictableProcessL2 F P →L[ℝ] PredictableProcessL2 (filtration A F) (ρ.prod P) := by
  let L := (timeLift (ρ := ρ) (P := P)).comp (PredictableProcessL2 F P).subtypeL
  refine L.codRestrict (PredictableProcessL2 (filtration A F) (ρ.prod P)) ?_
  intro U
  let hU := lpMeas.aestronglyMeasurable U
  have hsm : StronglyMeasurable[(filtration A F).predictable]
      (fun z => hU.mk (U : TimeProcessL2 P) (timeProjection z)) :=
    hU.stronglyMeasurable_mk.comp_measurable timeProjection_predictable
  have he : (L U : ℝ≥0 × (A × Ω) → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      (fun z => hU.mk (U : TimeProcessL2 P) (timeProjection z)) :=
    (timeLift_coe (ρ := ρ) (U : TimeProcessL2 P)).trans
      (timeProjection_measurePreserving.quasiMeasurePreserving.ae_eq_comp hU.ae_eq_mk)
  exact hsm.aestronglyMeasurable.congr he.symm

lemma predictableLift_coe (U : PredictableProcessL2 F P) :
    (predictableLift (ρ := ρ) U : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      (fun z => (U : TimeProcessL2 P) (timeProjection z)) := timeLift_coe _

/-- Actual adapted random-variable pullback at a deterministic time. -/
@[expose] def adaptedLift (t : ℝ≥0) (Z : lpMeas ℝ ℝ (F t) 2 P) :
    lpMeas ℝ ℝ (filtration A F t) 2 (ρ.prod P) := by
  let hZ := lpMeas.aestronglyMeasurable Z
  have hsm : StronglyMeasurable[filtration A F t]
      (fun q : A × Ω => hZ.mk (Z : RandomL2 P) q.2) :=
    hZ.stronglyMeasurable_mk.comp_measurable (base_known t)
  have he : (randomLift (ρ := ρ) (Z : RandomL2 P) : A × Ω → ℝ) =ᵐ[ρ.prod P]
      (fun q => hZ.mk (Z : RandomL2 P) q.2) :=
    (randomLift_coe (ρ := ρ) (Z : RandomL2 P)).trans
      (measurePreserving_snd.quasiMeasurePreserving.ae_eq_comp hZ.ae_eq_mk)
  exact ⟨randomLift (ρ := ρ) (Z : RandomL2 P),hsm.aestronglyMeasurable.congr he.symm⟩

lemma adaptedLift_coe (t : ℝ≥0) (Z : lpMeas ℝ ℝ (F t) 2 P) :
    (adaptedLift (ρ := ρ) t Z : RandomL2 (ρ.prod P)) =ᵐ[ρ.prod P]
      (fun q : A × Ω => (Z : RandomL2 P) q.2) := randomLift_coe _

lemma predictableLift_elementary (s t : ℝ≥0) (Z : lpMeas ℝ ℝ (F s) 2 P) :
    predictableLift (ρ := ρ) (elementaryPredictable F s t Z) =
      elementaryPredictable (filtration A F) s t (adaptedLift s Z) := by
  apply Subtype.ext
  apply Lp.ext
  have hz := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := ρ.prod P)).ae_eq_comp
    (adaptedLift_coe (ρ := ρ) s Z)
  have hel := (timeProjection_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp
    (elementaryPredictable_coeFn F s t Z)
  filter_upwards [predictableLift_coe (ρ := ρ) (elementaryPredictable F s t Z),
    elementaryPredictable_coeFn (filtration A F) s t (adaptedLift s Z),hz,hel] with z hL hR hz hel
  dsimp only [Function.comp_def] at hz hel
  rw [hL,hR,hel]
  change (if z.1 ∈ Ioc s t then (Z : RandomL2 P) z.2.2 else 0)=
    if z.1 ∈ Ioc s t then (adaptedLift (ρ := ρ) s Z : RandomL2 (ρ.prod P)) z.2 else 0
  by_cases h : z.1 ∈ Ioc s t
  · simp only [ite_eq_left h]
    exact hz.symm
  · simp only [ite_eq_right h]

lemma coordinateIto_lift_elementary (D : BrownianDriver N P F) (i : Fin N)
    {s t : ℝ≥0} (hst : s ≤ t) (Z : lpMeas ℝ ℝ (F s) 2 P) :
    coordinateIto (driver (ρ := ρ) D) i (predictableLift (elementaryPredictable F s t Z)) =
      randomLift (coordinateIto D i (elementaryPredictable F s t Z)) := by
  rw [predictableLift_elementary]
  unfold coordinateIto
  rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst),
    FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst)]
  apply Lp.ext
  have hbase := (measurePreserving_snd (μ := ρ) (ν := P)).quasiMeasurePreserving.ae_eq_comp
    (coeFn_elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z)
  filter_upwards [coeFn_elementaryBrownianValue ((driver (ρ := ρ) D).filtered i).toIsPreBrownianReal
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable i) ((driver (ρ := ρ) D).filtered i) hst (adaptedLift s Z),
    randomLift_coe (ρ := ρ) (elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z),hbase,adaptedLift_coe s Z]
    with q hprod hLift hbase hZ
  dsimp only [Function.comp_def] at hbase
  rw [hprod,hLift,hbase,hZ]
  rfl

/-- True operator commutation for every predictable L² integrand, proved
by density rather than assumed for the parameterized SDE. -/
theorem coordinateIto_predictableLift (D : BrownianDriver N P F) (i : Fin N)
    (U : PredictableProcessL2 F P) :
    coordinateIto (driver (ρ := ρ) D) i (predictableLift U) = randomLift (coordinateIto D i U) := by
  let L := (coordinateIto (driver (ρ := ρ) D) i).comp (predictableLift (ρ := ρ))
  let R := (randomLift (ρ := ρ)).comp (coordinateIto D i)
  change L U=R U
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P) F).induction_on U
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have he (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex F P) :
      L (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x)=R (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x) :=
    coordinateIto_lift_elementary D i x.2.1.2 x.2.2
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable F P v=
      ∑ x ∈ v.support, v x • FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,Finsupp.linearCombination_apply,Finsupp.sum]
  rw [hv,map_sum,map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun Y => v x • Y) (he x))

end SphericalAging.BackgroundItoLift
