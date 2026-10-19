module

public import OverlapPaper.DSFiniteGram
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section

/-! The compact coordinate unit ball used for the directing-measure limit.
Its topology is the coordinate topology. Every point nevertheless represents
a genuine norm-at-most-one vector of ℓ², and this representation is strongly
measurable in the norm topology. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

abbrev DSCoordinates := ℕ → Icc (-1:ℝ) 1

def DSCoordinateBallSet : Set DSCoordinates :=
  {v | ∀ s : Finset ℕ,∑ i ∈ s,(v i : ℝ)^2 ≤ 1}

theorem isClosed_DSCoordinateBallSet : IsClosed DSCoordinateBallSet := by
  have he : DSCoordinateBallSet = ⋂ s : Finset ℕ,
      {v : DSCoordinates | ∑ i ∈ s,(v i : ℝ)^2 ≤ 1} := by
    ext v
    simp [DSCoordinateBallSet]
  rw [he]
  apply isClosed_iInter
  intro s
  exact isClosed_le (by fun_prop) continuous_const

abbrev DSCoordinateBall := DSCoordinateBallSet

instance : CompactSpace DSCoordinateBall := isCompact_iff_compactSpace.mp isClosed_DSCoordinateBallSet.isCompact

instance : Nonempty DSCoordinateBall := by
  refine ⟨⟨fun _ => ⟨0,by norm_num⟩,?_⟩⟩
  intro s
  simp

abbrev DSHilbert := ℓ²(ℕ,ℝ)

def coordinateVector (v : DSCoordinateBall) : DSHilbert :=
  ⟨fun i => (v.1 i : ℝ),memℓp_gen' (C := 1) (fun s => by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using v.2 s)⟩

@[simp] theorem coordinateVector_apply (v : DSCoordinateBall) (i : ℕ) :
    coordinateVector v i = (v.1 i : ℝ) := rfl

theorem coordinateVector_norm_le_one (v : DSCoordinateBall) : ‖coordinateVector v‖ ≤ 1 := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal) zero_le_one
  intro s
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,one_pow,
    coordinateVector_apply] using v.2 s

theorem coordinateVector_injective : Function.Injective coordinateVector := by
  intro v w h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg (fun x : DSHilbert => x i) h

theorem stronglyMeasurable_coordinateVector : StronglyMeasurable coordinateVector := by
  let f : ℕ → DSCoordinateBall → DSHilbert := fun n v =>
    ∑ i ∈ Finset.range n,lp.single 2 i (v.1 i : ℝ)
  have hc (n : ℕ) : Continuous (f n) := by
    apply continuous_finsetSum
    intro i _
    exact (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ℕ => ℝ) 2 i).continuous.comp
      ((continuous_subtype_val : Continuous (fun u : Icc (-1:ℝ) 1 => (u:ℝ))).comp
        ((continuous_apply i : Continuous (fun v : DSCoordinates => v i)).comp
          (continuous_subtype_val : Continuous (fun v : DSCoordinateBall => v.1))))
  have ht : Tendsto f atTop (𝓝 coordinateVector) := by
    apply tendsto_pi_nhds.mpr
    intro v
    exact (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ∞) (coordinateVector v)).tendsto_sum_nat
  exact stronglyMeasurable_of_tendsto atTop (fun n => (hc n).stronglyMeasurable) ht

end OverlapPaper
