module

public import SphericalAging.BackgroundItoLift

public section

/-! Naturality of the actual Itô operator under an arbitrary
measure-preserving filtered sample map. Elementary stochastic values
commute with pullback because the driving coordinates do; density then
proves the identity for every actual predictable L² integrand. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.FilteredItoPullback
open HardSphereDynamics VectorIto
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'} {N : ℕ}
  {φ : Ω' → Ω} (hφ : MeasurePreserving φ Q P)
  (hF : ∀ t, @Measurable Ω' Ω (G t) (F t) φ)

/-- Retain time and apply the actual filtered sample map. -/
@[expose] def timeMap (φ : Ω' → Ω) (z : ℝ≥0 × Ω') : ℝ≥0 × Ω := (z.1,φ z.2)

include hφ in
lemma timeMap_measurePreserving :
    MeasurePreserving (timeMap φ) (nonnegativeLebesgueMeasure.prod Q)
      (nonnegativeLebesgueMeasure.prod P) :=
  (MeasurePreserving.id nonnegativeLebesgueMeasure).prod hφ

include hF in
lemma timeMap_predictable :
    @Measurable (ℝ≥0 × Ω') (ℝ≥0 × Ω) G.predictable F.predictable (timeMap φ) := by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro S hS
    change MeasurableSet[G.predictable] ((timeMap φ) ⁻¹' ({0} ×ˢ S))
    convert measurableSet_predictable_singleton_bot_prod (𝓕 := G)
      ((hF 0) hS) using 1
    ext z
    simp [timeMap]
  · intro t S hS
    change MeasurableSet[G.predictable] ((timeMap φ) ⁻¹' (Ioi t ×ˢ S))
    convert measurableSet_predictable_Ioi_prod (𝓕 := G) ((hF t) hS) using 1
    ext z
    simp [timeMap]

/-- Isometric pullback of actual random variables. -/
@[expose] def randomPullback : RandomL2 P →L[ℝ] RandomL2 Q :=
  (Lp.compMeasurePreservingₗᵢ ℝ φ hφ).toContinuousLinearMap

lemma randomPullback_coe (Z : RandomL2 P) :
    (randomPullback hφ Z : Ω' → ℝ) =ᵐ[Q] (fun ω => Z (φ ω)) :=
  Lp.coeFn_compMeasurePreserving Z hφ

/-- Isometric pullback of actual time/sample random fields. -/
@[expose] def timePullback : TimeProcessL2 P →L[ℝ] TimeProcessL2 Q :=
  (Lp.compMeasurePreservingₗᵢ ℝ (timeMap φ) (timeMap_measurePreserving hφ)).toContinuousLinearMap

lemma timePullback_coe (U : TimeProcessL2 P) :
    (timePullback hφ U : ℝ≥0 × Ω' → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod Q]
      (fun z => U (timeMap φ z)) :=
  Lp.coeFn_compMeasurePreserving U (timeMap_measurePreserving hφ)

/-- The same isometry with its actual predictable codomain. -/
@[expose] def predictablePullback : PredictableProcessL2 F P →L[ℝ] PredictableProcessL2 G Q := by
  let L := (timePullback hφ).comp (PredictableProcessL2 F P).subtypeL
  refine L.codRestrict (PredictableProcessL2 G Q) ?_
  intro U
  let hU := lpMeas.aestronglyMeasurable U
  have hsm : StronglyMeasurable[G.predictable]
      (fun z => hU.mk (U : TimeProcessL2 P) (timeMap φ z)) :=
    hU.stronglyMeasurable_mk.comp_measurable (timeMap_predictable hF)
  have he : (L U : ℝ≥0 × Ω' → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod Q]
      (fun z => hU.mk (U : TimeProcessL2 P) (timeMap φ z)) :=
    (timePullback_coe hφ (U : TimeProcessL2 P)).trans
      ((timeMap_measurePreserving hφ).quasiMeasurePreserving.ae_eq_comp hU.ae_eq_mk)
  exact hsm.aestronglyMeasurable.congr he.symm

lemma predictablePullback_coe (U : PredictableProcessL2 F P) :
    (predictablePullback hφ hF U : TimeProcessL2 Q) =ᵐ[nonnegativeLebesgueMeasure.prod Q]
      (fun z => (U : TimeProcessL2 P) (timeMap φ z)) := timePullback_coe hφ _

/-- Pullback of a genuinely F_t-measurable random variable. -/
@[expose] def adaptedPullback (t : ℝ≥0) (Z : lpMeas ℝ ℝ (F t) 2 P) : lpMeas ℝ ℝ (G t) 2 Q := by
  let hZ := lpMeas.aestronglyMeasurable Z
  have hsm : StronglyMeasurable[G t] (fun ω => hZ.mk (Z : RandomL2 P) (φ ω)) :=
    hZ.stronglyMeasurable_mk.comp_measurable (hF t)
  have he : (randomPullback hφ (Z : RandomL2 P) : Ω' → ℝ) =ᵐ[Q]
      (fun ω => hZ.mk (Z : RandomL2 P) (φ ω)) :=
    (randomPullback_coe hφ (Z : RandomL2 P)).trans
      (hφ.quasiMeasurePreserving.ae_eq_comp hZ.ae_eq_mk)
  exact ⟨randomPullback hφ (Z : RandomL2 P),hsm.aestronglyMeasurable.congr he.symm⟩

lemma adaptedPullback_coe (t : ℝ≥0) (Z : lpMeas ℝ ℝ (F t) 2 P) :
    (adaptedPullback hφ hF t Z : RandomL2 Q) =ᵐ[Q] (fun ω => (Z : RandomL2 P) (φ ω)) :=
  randomPullback_coe hφ _

lemma predictablePullback_elementary (s t : ℝ≥0) (Z : lpMeas ℝ ℝ (F s) 2 P) :
    predictablePullback hφ hF (elementaryPredictable F s t Z) =
      elementaryPredictable G s t (adaptedPullback hφ hF s Z) := by
  apply Subtype.ext
  apply Lp.ext
  have hz := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := Q)).ae_eq_comp
    (adaptedPullback_coe hφ hF s Z)
  have hel := (timeMap_measurePreserving hφ).quasiMeasurePreserving.ae_eq_comp
    (elementaryPredictable_coeFn F s t Z)
  filter_upwards [predictablePullback_coe hφ hF (elementaryPredictable F s t Z),
    elementaryPredictable_coeFn G s t (adaptedPullback hφ hF s Z),hz,hel] with z hL hR hz hel
  dsimp only [Function.comp_def] at hz hel
  rw [hL,hR,hel]
  change (if z.1 ∈ Ioc s t then (Z : RandomL2 P) (φ z.2) else 0)=
    if z.1 ∈ Ioc s t then (adaptedPullback hφ hF s Z : RandomL2 Q) z.2 else 0
  by_cases h : z.1 ∈ Ioc s t
  · simp only [ite_eq_left h]
    exact hz.symm
  · simp only [ite_eq_right h]

lemma coordinateIto_pullback_elementary (D : BrownianDriver N P F)
    (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q] (fun ω => D.coordinate i t (φ ω)))
    (i : Fin N) {s t : ℝ≥0} (hst : s ≤ t) (Z : lpMeas ℝ ℝ (F s) 2 P) :
    coordinateIto E i (predictablePullback hφ hF (elementaryPredictable F s t Z)) =
      randomPullback hφ (coordinateIto D i (elementaryPredictable F s t Z)) := by
  rw [predictablePullback_elementary]
  unfold coordinateIto
  rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst),
    FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable (hab := hst)]
  apply Lp.ext
  have hbase := hφ.quasiMeasurePreserving.ae_eq_comp
    (coeFn_elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z)
  filter_upwards [coeFn_elementaryBrownianValue (E.filtered i).toIsPreBrownianReal
      (E.coordinateStronglyMeasurable i) (E.filtered i) hst (adaptedPullback hφ hF s Z),
    randomPullback_coe hφ (elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hst Z),hbase,
    adaptedPullback_coe hφ hF s Z,hB i t,hB i s]
    with ω hprod hLift hbase hZ ht hs
  dsimp only [Function.comp_def] at hbase
  rw [hprod,hLift,hbase,hZ]
  change _ * (E.coordinate i t ω-E.coordinate i s ω) = _
  rw [ht,hs]

/-- Naturality for all predictable L² integrands, proved from actual
Brownian coordinates and elementary approximation. -/
theorem coordinateIto_predictablePullback (D : BrownianDriver N P F)
    (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q] (fun ω => D.coordinate i t (φ ω)))
    (i : Fin N) (U : PredictableProcessL2 F P) :
    coordinateIto E i (predictablePullback hφ hF U) = randomPullback hφ (coordinateIto D i U) := by
  let L := (coordinateIto E i).comp (predictablePullback hφ hF)
  let R := (randomPullback hφ).comp (coordinateIto D i)
  change L U=R U
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P) F).induction_on U
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have he (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex F P) :
      L (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x)=R (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x) :=
    coordinateIto_pullback_elementary hφ hF D E hB i x.2.1.2 x.2.2
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable F P v=
      ∑ x ∈ v.support, v x • FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,Finsupp.linearCombination_apply,Finsupp.sum]
  rw [hv,map_sum,map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun Y => v x • Y) (he x))

/-- The actual whole matrix-row stochastic integral also commutes. -/
theorem vectorIto_predictablePullback (D : BrownianDriver N P F)
    (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q] (fun ω => D.coordinate i t (φ ω)))
    (U : Fin N → PredictableProcessL2 F P) :
    vectorIto E (fun i => predictablePullback hφ hF (U i)) =
      randomPullback hφ (vectorIto D U) := by
  simp only [vectorIto,map_sum,coordinateIto_predictablePullback hφ hF D E hB]

/-- Deterministic time restriction retains its literal interval under pullback. -/
theorem predictableTimeRestrict_pullback (t : ℝ≥0) (U : PredictableProcessL2 F P) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict G t (predictablePullback hφ hF U) =
      predictablePullback hφ hF (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U) := by
  apply Subtype.ext
  apply Lp.ext
  have he := (timeMap_measurePreserving hφ).quasiMeasurePreserving.ae_eq_comp
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t U)
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn G t
      (predictablePullback hφ hF U),predictablePullback_coe hφ hF U,
    predictablePullback_coe hφ hF (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U),he]
    with z hL hU hR he
  dsimp only [Function.comp_def] at he
  rw [hL,hR,he]
  simp only [FourPapersCommon.FilteredBrownian.predictableTimeFrame,Set.indicator,
    Set.mem_prod,Set.mem_univ,and_true,timeMap,hU,Function.comp_def]

/-- Actual terminal Itô processes commute with filtered sample pullback. -/
theorem vectorProcessLp_pullback (D : BrownianDriver N P F)
    (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q] (fun ω => D.coordinate i t (φ ω)))
    (U : Fin N → PredictableProcessL2 F P) (t : ℝ≥0) :
    vectorProcessLp E (fun i => predictablePullback hφ hF (U i)) t =
      randomPullback hφ (vectorProcessLp D U t) := by
  unfold vectorProcessLp
  simp only [predictableTimeRestrict_pullback hφ hF]
  exact vectorIto_predictablePullback hφ hF D E hB _

end SphericalAging.FilteredItoPullback
