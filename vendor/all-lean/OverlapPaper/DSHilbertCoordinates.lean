module

public import OverlapPaper.DSCoordinateBall
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! The compact coordinate ball and the genuine Hilbert unit ball have the
same Borel structure. Compactness uses coordinates; the directing measure
obtained from it still lives in the actual normed Hilbert space ℓ². -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal lp BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem dense_span_DSHilbert_basis :
    Dense (Submodule.span ℝ (range (fun i : ℕ => (lp.single 2 i 1 : DSHilbert))) : Set DSHilbert) := by
  rw [dense_iff_closure_eq]
  apply eq_univ_of_forall
  intro v
  apply isClosed_closure.mem_of_tendsto
    ((lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ∞) v).tendsto_sum_nat)
  apply Eventually.of_forall
  intro n
  apply subset_closure
  apply Submodule.sum_mem
  intro i _
  have hb : (lp.single 2 i 1 : DSHilbert) ∈
      Submodule.span ℝ (range (fun j : ℕ => (lp.single 2 j 1 : DSHilbert))) :=
    Submodule.subset_span (mem_range_self i)
  have hm := Submodule.smul_mem
    (Submodule.span ℝ (range (fun j : ℕ => (lp.single 2 j 1 : DSHilbert)))) (v i) hb
  simpa only [←lp.single_smul,smul_eq_mul,mul_one] using hm

instance : SeparableSpace DSHilbert := by
  apply dense_span_DSHilbert_basis.isSeparable_iff.mp
  exact (countable_range (fun i : ℕ => (lp.single 2 i 1 : DSHilbert))).isSeparable.span

instance : SecondCountableTopology DSHilbert := UniformSpace.secondCountable_of_separable _

instance : MeasurableSpace DSHilbert := borel DSHilbert
instance : BorelSpace DSHilbert := ⟨rfl⟩

theorem measurable_coordinateVector : Measurable coordinateVector :=
  stronglyMeasurable_coordinateVector.measurable

abbrev DSNormBall := {v : DSHilbert // ‖v‖ ≤ 1}

def hilbertUnitCoordinates (v : DSNormBall) : DSCoordinateBall :=
  ⟨fun i => ⟨v.1 i,by
      have hi : ‖v.1 i‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) v.1 i).trans v.2
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hi⟩,
    fun s => by
      have hsum := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) v.1 s
      have hn : ‖v.1‖^2 ≤ 1 := by nlinarith [norm_nonneg v.1,v.2]
      have hsum' : ∑ i ∈ s,(v.1 i)^2 ≤ ‖v.1‖^2 := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hsum
      exact hsum'.trans hn⟩

def coordinatesUnitHilbert (v : DSCoordinateBall) : DSNormBall :=
  ⟨coordinateVector v,coordinateVector_norm_le_one v⟩

theorem coordinatesUnitHilbert_leftInverse : Function.LeftInverse coordinatesUnitHilbert hilbertUnitCoordinates := by
  intro v
  apply Subtype.ext
  ext i
  rfl

theorem coordinatesUnitHilbert_rightInverse : Function.RightInverse coordinatesUnitHilbert hilbertUnitCoordinates := by
  intro v
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rfl

theorem continuous_hilbertUnitCoordinates : Continuous hilbertUnitCoordinates := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).continuous.comp continuous_subtype_val

theorem measurable_coordinatesUnitHilbert : Measurable coordinatesUnitHilbert :=
  measurable_coordinateVector.subtype_mk

def coordinateHilbertMeasurableEquiv : DSCoordinateBall ≃ᵐ DSNormBall where
  toFun := coordinatesUnitHilbert
  invFun := hilbertUnitCoordinates
  left_inv := coordinatesUnitHilbert_rightInverse
  right_inv := coordinatesUnitHilbert_leftInverse
  measurable_toFun := measurable_coordinatesUnitHilbert
  measurable_invFun := continuous_hilbertUnitCoordinates.measurable

end OverlapPaper
