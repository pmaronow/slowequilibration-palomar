module
public import FRSB.StochasticDiagonal

@[expose] public section

/-! Explicit strictly interior crops, converging to closed cell endpoints. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace FRSB
 def cellCropRadius (a b : ℝ) (n : ℕ) : ℝ := (b-a)/((n:ℝ)+2)
 def leftCellCrop (a b : ℝ) (n : ℕ) : ℝ≥0 := (a+cellCropRadius a b n).toNNReal
 def rightCellCrop (a b : ℝ) (n : ℕ) : ℝ≥0 := (b-cellCropRadius a b n).toNNReal

 theorem cellCrop_bounds {a b : ℝ} (ha : 0≤a) (hab : a<b) (n : ℕ) :
    a<(leftCellCrop a b n : ℝ) ∧ leftCellCrop a b n≤rightCellCrop a b n ∧
      (rightCellCrop a b n : ℝ)<b := by
  have hn : 0 < (n:ℝ)+2 := by positivity
  have hn2 : 2 ≤ (n:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : 0 < cellCropRadius a b n := div_pos (sub_pos.mpr hab) hn
  have hd2 : 2*cellCropRadius a b n ≤ b-a := by
    unfold cellCropRadius
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hn2 (sub_nonneg.mpr hab.le)]
  have hl : 0≤a+cellCropRadius a b n := by linarith
  have hr : 0≤b-cellCropRadius a b n := by linarith
  simp only [leftCellCrop,rightCellCrop,Real.coe_toNNReal _ hl,Real.coe_toNNReal _ hr]
  constructor
  · linarith
  constructor
  · exact Real.toNNReal_mono (show a+cellCropRadius a b n≤b-cellCropRadius a b n by linarith)
  · linarith

 theorem tendsto_leftCellCrop {a b : ℝ} (ha : 0≤a) (hab : a<b) :
    Tendsto (leftCellCrop a b) atTop (nhds a.toNNReal) := by
  have hd : Tendsto (cellCropRadius a b) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun n => a+cellCropRadius a b n) atTop (nhds a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hd)
  exact (continuous_real_toNNReal.tendsto a).comp hh

 theorem tendsto_rightCellCrop {a b : ℝ} (ha : 0≤a) (hab : a<b) :
    Tendsto (rightCellCrop a b) atTop (nhds b.toNNReal) := by
  have hd : Tendsto (cellCropRadius a b) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun n => b-cellCropRadius a b n) atTop (nhds b) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hd)
  exact (continuous_real_toNNReal.tendsto b).comp hh


end FRSB
