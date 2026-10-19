module

public import SphericalAging.ShiftedBrownian
public import Mathlib.MeasureTheory.Group.Integral

public section

/-! Exact time translation of the genuine nonnegative Lebesgue product
measure. Pullback after a waiting time contracts ambient L², preserving
actual representatives and null sets. -/
noncomputable section
open MeasureTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.TimeShiftMeasure
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
set_option maxHeartbeats 800000

lemma map_coe_nonnegativeLebesgue :
    nonnegativeLebesgueMeasure.map ((↑) : ℝ≥0 → ℝ)=
      (volume : Measure ℝ).restrict (Ici 0) := by
  rw [nonnegativeLebesgueMeasure,measurableEmbedding_nnrealCoe_iterated.map_comap,NNReal.range_coe]

/-- Translation by `s` sends nonnegative Lebesgue measure to its literal
restriction to `[s,∞)`. -/
lemma map_add (s : ℝ≥0) : nonnegativeLebesgueMeasure.map (fun t => s+t)=
    nonnegativeLebesgueMeasure.restrict (Ici s) := by
  apply measurableEmbedding_nnrealCoe_iterated.map_injective
  rw [Measure.map_map NNReal.continuous_coe.measurable (by fun_prop)]
  have he : (((↑) : ℝ≥0 → ℝ) ∘ (fun t => s+t))=
      ((fun r : ℝ => (s : ℝ)+r) ∘ ((↑) : ℝ≥0 → ℝ)) := by
    funext t
    simp
  rw [he,← Measure.map_map (by fun_prop) NNReal.continuous_coe.measurable,map_coe_nonnegativeLebesgue]
  have hpre : (fun r : ℝ => (s : ℝ)+r) ⁻¹' Ici (s : ℝ)=Ici 0 := by
    ext r
    simp
  have hpre' : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ici (s : ℝ)=Ici s := by
    ext r
    simp
  rw [← hpre',← measurableEmbedding_nnrealCoe_iterated.restrict_map,
    map_coe_nonnegativeLebesgue,Measure.restrict_restrict measurableSet_Ici]
  have hinter : Ici (s : ℝ) ∩ Ici 0=Ici (s : ℝ) := by
    exact inter_eq_left.mpr (Ici_subset_Ici.mpr s.coe_nonneg)
  rw [hinter,← hpre,← Measure.restrict_map (by fun_prop : Measurable (fun r : ℝ => (s : ℝ)+r)) measurableSet_Ici,
    (measurePreserving_add_left (volume : Measure ℝ) (s : ℝ)).map_eq]

lemma map_add_le (s : ℝ≥0) : nonnegativeLebesgueMeasure.map (fun t => s+t)≤
    nonnegativeLebesgueMeasure := by rw [map_add];exact Measure.restrict_le_self

/-- Time translation preserves the actual sample coordinate. -/
@[expose] def shift (s : ℝ≥0) (q : ℝ≥0 × Ω) : ℝ≥0 × Ω := (s+q.1,q.2)

lemma shift_measurable (s : ℝ≥0) : Measurable (shift (Ω := Ω) s) := by
  exact ((measurable_const.add measurable_fst).prodMk measurable_snd)

lemma map_shift_le (s : ℝ≥0) : (nonnegativeLebesgueMeasure.prod P).map (shift s)≤
    nonnegativeLebesgueMeasure.prod P := by
  change (nonnegativeLebesgueMeasure.prod P).map (Prod.map (fun t => s+t) id)≤_
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  exact Measure.prod_mono (map_add_le s) le_rfl

lemma shift_quasiMeasurePreserving (s : ℝ≥0) : Measure.QuasiMeasurePreserving (shift s)
    (nonnegativeLebesgueMeasure.prod P) (nonnegativeLebesgueMeasure.prod P) :=
  ⟨shift_measurable s,Measure.absolutelyContinuous_of_le (map_shift_le s)⟩

/-- Actual bounded pullback operator on ambient time/sample L². -/
@[expose] def timeShift (s : ℝ≥0) : TimeProcessL2 P →L[ℝ] TimeProcessL2 P :=
  ((Lp.compMeasurePreservingₗᵢ ℝ (shift s)
    (⟨shift_measurable s,rfl⟩ : MeasurePreserving (shift s)
      (nonnegativeLebesgueMeasure.prod P) ((nonnegativeLebesgueMeasure.prod P).map (shift s)))).toContinuousLinearMap).comp
    (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ∞)
      (by simpa using map_shift_le (P := P) s))

lemma timeShift_coe (s : ℝ≥0) (U : TimeProcessL2 P) :
    (timeShift s U : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => U (shift s q)) := by
  let hc : (1 : ℝ≥0∞) ≠ ∞ := by simp
  let hle : (nonnegativeLebesgueMeasure.prod P).map (shift s)≤
      (1 : ℝ≥0∞) • (nonnegativeLebesgueMeasure.prod P) := by simpa using map_shift_le (P := P) s
  let V := Lp.LpToLpOfMeasureLeSMul hc hle U
  have h1 := Lp.coeFn_compMeasurePreserving V
    (⟨shift_measurable s,rfl⟩ : MeasurePreserving (shift s)
      (nonnegativeLebesgueMeasure.prod P) ((nonnegativeLebesgueMeasure.prod P).map (shift s)))
  have h2 := (shift_measurable (Ω := Ω) s).quasiMeasurePreserving (nonnegativeLebesgueMeasure.prod P)
    |>.ae_eq_comp (Lp.coeFn_LpToLpOfMeasureLeSMul hc hle U)
  exact h1.trans h2

lemma timeShift_norm_le (s : ℝ≥0) (U : TimeProcessL2 P) : ‖timeShift s U‖≤‖U‖ := by
  let hc : (1 : ℝ≥0∞) ≠ ∞ := by simp
  let hle : (nonnegativeLebesgueMeasure.prod P).map (shift s)≤
      (1 : ℝ≥0∞) • (nonnegativeLebesgueMeasure.prod P) := by simpa using map_shift_le (P := P) s
  let L : TimeProcessL2 P →L[ℝ] Lp ℝ 2 ((nonnegativeLebesgueMeasure.prod P).map (shift s)) :=
    Lp.LpToLpOfMeasureLeSMul hc hle
  let hpres : MeasurePreserving (shift s) (nonnegativeLebesgueMeasure.prod P)
      ((nonnegativeLebesgueMeasure.prod P).map (shift s)) := ⟨shift_measurable s,rfl⟩
  change ‖Lp.compMeasurePreserving (shift s) hpres (L U)‖≤‖U‖
  rw [Lp.norm_compMeasurePreserving]
  have hnorm : ‖L‖ ≤ 1 := by
    simpa using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := (2 : ℝ≥0∞)) hc hle
  exact (ContinuousLinearMap.le_opNorm L U).trans (by simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg U))

end SphericalAging.TimeShiftMeasure
