module

public import SphericalAging.TimeShiftMeasure

public section

/-! Genuine predictable L² time translation. The enlarged shifted past
is used at every time; the time-zero discrepancy of translated elementary
processes is removed only using the actual null singleton of Lebesgue
measure. -/
noncomputable section
open MeasureTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedPredictable
open TimeShiftMeasure
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 900000

lemma measurable_univ_prod {G : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {A : Set Ω}
    (hA : MeasurableSet[G 0] A) : MeasurableSet[G.predictable] (univ ×ˢ A) := by
  have he : (univ : Set ℝ≥0) ×ˢ A=({0} ×ˢ A) ∪ (Ioi 0 ×ˢ A) := by
    ext q
    simp only [mem_prod,mem_univ,true_and,mem_union,mem_singleton_iff,mem_Ioi]
    constructor
    · intro h
      rcases eq_or_lt_of_le (zero_le : 0 ≤ q.1) with ht | ht
      · exact .inl ⟨ht.symm,h⟩
      · exact .inr ⟨ht,h⟩
    · rintro (⟨_,h⟩ | ⟨_,h⟩) <;> exact h
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod hA).union
    (measurableSet_predictable_Ioi_prod hA)

/-- Translating a genuinely predictable process remains predictable for
`F_s(t)=F(s+t)`. -/
lemma shift_predictable (s : ℝ≥0) :
    @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) (ShiftedBrownian.filtration F s).predictable F.predictable (shift s) := by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[(ShiftedBrownian.filtration F s).predictable]
      (shift s ⁻¹' ({0} ×ˢ A))
    by_cases hs : s=0
    · subst s
      have ha0 : MeasurableSet[ShiftedBrownian.filtration F 0 0] A := by
        rw [ShiftedBrownian.filtration_zero]
        exact hA
      convert measurableSet_predictable_singleton_bot_prod (𝓕 := ShiftedBrownian.filtration F 0)
        ha0 using 1
      ext q
      simp [shift]
    · have he : (shift s : ℝ≥0 × Ω → ℝ≥0 × Ω) ⁻¹' ({0} ×ˢ A)=∅ := by
        ext q
        simp only [mem_preimage,mem_prod,mem_singleton_iff,shift,mem_empty_iff_false,iff_false,not_and]
        intro h
        exact False.elim (hs (le_antisymm ((le_add_right le_rfl).trans_eq h) (zero_le : 0 ≤ s)))
      rw [he]
      exact @MeasurableSet.empty _ (ShiftedBrownian.filtration F s).predictable
  · intro a A hA
    change MeasurableSet[(ShiftedBrownian.filtration F s).predictable]
      (shift s ⁻¹' (Ioi a ×ˢ A))
    by_cases hsa : s ≤ a
    · have he : (shift s : ℝ≥0 × Ω → ℝ≥0 × Ω) ⁻¹' (Ioi a ×ˢ A)=Ioi (a-s) ×ˢ A := by
        ext q
        simp only [mem_preimage,mem_prod,mem_Ioi,shift]
        rw [tsub_lt_iff_left hsa]
      rw [he]
      apply measurableSet_predictable_Ioi_prod
      change MeasurableSet[F (s+(a-s))] A
      rw [add_tsub_cancel_of_le hsa]
      exact hA
    · have has : a < s := lt_of_not_ge hsa
      have he : (shift s : ℝ≥0 × Ω → ℝ≥0 × Ω) ⁻¹' (Ioi a ×ˢ A)=univ ×ˢ A := by
        ext q
        simp only [mem_preimage,mem_prod,mem_Ioi,shift,mem_univ,true_and]
        exact and_iff_right (has.trans_le (le_add_right le_rfl))
      rw [he]
      apply measurable_univ_prod
      rw [ShiftedBrownian.filtration_zero]
      exact F.mono has.le A hA

/-- Bounded true time-translation operator between actual predictable
L² spaces. -/
@[expose] def predictableShift (s : ℝ≥0) : PredictableProcessL2 F P →L[ℝ]
    PredictableProcessL2 (ShiftedBrownian.filtration F s) P := by
  let L := (timeShift (P := P) s).comp (PredictableProcessL2 F P).subtypeL
  refine L.codRestrict (PredictableProcessL2 (ShiftedBrownian.filtration F s) P) ?_
  intro U
  let hU := lpMeas.aestronglyMeasurable U
  have hsm : StronglyMeasurable[(ShiftedBrownian.filtration F s).predictable]
      (fun q => hU.mk (U : TimeProcessL2 P) (shift s q)) :=
    hU.stronglyMeasurable_mk.comp_measurable (shift_predictable s)
  have he : (L U : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => hU.mk (U : TimeProcessL2 P) (shift s q)) :=
    (timeShift_coe s (U : TimeProcessL2 P)).trans
      ((shift_quasiMeasurePreserving s).ae_eq_comp hU.ae_eq_mk)
  exact hsm.aestronglyMeasurable.congr he.symm

lemma predictableShift_coe (s : ℝ≥0) (U : PredictableProcessL2 F P) :
    (predictableShift s U : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => (U : TimeProcessL2 P) (shift s q)) := timeShift_coe s (U : TimeProcessL2 P)

lemma predictableShift_norm_le (s : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖predictableShift s U‖≤‖U‖ := timeShift_norm_le s (U : TimeProcessL2 P)

/-- An original adapted scalar remains adapted at the translated left
endpoint, even if that endpoint falls before the waiting time. -/
@[expose] def adaptedShift (s a : ℝ≥0) (Z : lpMeas ℝ ℝ (F a) 2 P) :
    lpMeas ℝ ℝ (ShiftedBrownian.filtration F s (a-s)) 2 P :=
  ⟨(Z : RandomL2 P),(lpMeas.aestronglyMeasurable Z).mono (F.mono le_add_tsub)⟩

lemma translated_Ioc {s a b u : ℝ≥0} (hu : 0 < u) :
    s+u ∈ Ioc a b ↔ u ∈ Ioc (a-s) (b-s) := by
  simp only [mem_Ioc]
  have hlo : a < s+u ↔ a-s < u := by
    by_cases hsa : s ≤ a
    · exact (tsub_lt_iff_left hsa).symm
    · rw [tsub_eq_zero_of_le (le_of_not_ge hsa)]
      exact iff_of_true ((lt_of_not_ge hsa).trans_le (le_add_right le_rfl)) hu
  have hhi : s+u ≤ b ↔ u ≤ b-s := by
    by_cases hsb : s ≤ b
    · exact (le_tsub_iff_left hsb).symm
    · rw [tsub_eq_zero_of_le (le_of_not_ge hsb)]
      exact iff_of_false (not_le.mpr ((lt_of_not_ge hsb).trans_le (le_add_right le_rfl))) (not_le.mpr hu)
  exact and_congr hlo hhi

/-- Actual translation of elementary adapted integrands. The omitted
origin has zero nonnegative Lebesgue measure. -/
lemma predictableShift_elementary (s a b : ℝ≥0) (Z : lpMeas ℝ ℝ (F a) 2 P) :
    predictableShift s (elementaryPredictable F a b Z)=
      elementaryPredictable (ShiftedBrownian.filtration F s) (a-s) (b-s) (adaptedShift s a Z) := by
  apply Subtype.ext
  apply Lp.ext
  have hel := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp (elementaryPredictable_coeFn F a b Z)
  have hpos : ∀ᵐ q : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P,0 < q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [predictableShift_coe s (elementaryPredictable F a b Z),hel,
    elementaryPredictable_coeFn (ShiftedBrownian.filtration F s) (a-s) (b-s) (adaptedShift s a Z),hpos]
    with q hL hel hR hpos
  dsimp only [Function.comp_def] at hel
  rw [hL,hel,hR]
  simp only [shift,translated_Ioc hpos]
  rfl

end SphericalAging.ShiftedPredictable
