module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! Sharp L²--L⁸ interpolation to L⁴ on arbitrary measures, including the
uniform eighth-moment convergence theorem needed for random response fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.LpEightInterpolation
variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}

theorem eLpNorm_four_le (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ≤eLpNorm f 2 μ^((1:ℝ)/3)*eLpNorm f 8 μ^((2:ℝ)/3) := by
  let g : α → ℝ := fun x => ‖f x‖^((1:ℝ)/3)
  let h : α → ℝ := fun x => ‖f x‖^((2:ℝ)/3)
  have hg : AEStronglyMeasurable g μ :=
    (Real.continuous_rpow_const (by norm_num : 0≤(1:ℝ)/3)).comp_aestronglyMeasurable hf.norm
  have hh : AEStronglyMeasurable h μ :=
    (Real.continuous_rpow_const (by norm_num : 0≤(2:ℝ)/3)).comp_aestronglyMeasurable hf.norm
  letI : ENNReal.HolderTriple (6:ℝ≥0∞) 12 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p:=6) (q:=12) (r:=4)
    (fun a b : ℝ => a*b) 1 continuous_mul hg hh
    (Eventually.of_forall (fun x => by simp only [norm_mul,NNReal.coe_one,one_mul]; exact le_rfl))
  have he : (fun x => g x*h x)=(fun x => ‖f x‖) := by
    funext x
    dsimp [g,h]
    rw [←Real.rpow_add' (norm_nonneg _) (by norm_num : (1:ℝ)/3+2/3≠0)]
    norm_num
  rw [he,eLpNorm_norm f hf] at hb
  change eLpNorm f 4 μ≤1*eLpNorm (fun x => ‖f x‖^((1:ℝ)/3)) 6 μ*
    eLpNorm (fun x => ‖f x‖^((2:ℝ)/3)) 12 μ at hb
  rw [eLpNorm_norm_rpow f hf (by norm_num : 0<(1:ℝ)/3),
    eLpNorm_norm_rpow f hf (by norm_num : 0<(2:ℝ)/3)] at hb
  have h6 : (6:ℝ≥0∞)*ENNReal.ofReal ((1:ℝ)/3)=2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_ofReal]
  have h12 : (12:ℝ≥0∞)*ENNReal.ofReal ((2:ℝ)/3)=8 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_ofReal]
  rw [h6,h12,one_mul] at hb
  exact hb

theorem memLp_four (h2 : MemLp f 2 μ) (h8 : MemLp f 8 μ) : MemLp f 4 μ := by
  apply (eLpNorm_four_le h2.aestronglyMeasurable).trans_lt
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h8.eLpNorm_ne_top)

theorem lpNorm_four_le (h2 : MemLp f 2 μ) (h8 : MemLp f 8 μ) :
    lpNorm f 4 μ≤lpNorm f 2 μ^((1:ℝ)/3)*lpNorm f 8 μ^((2:ℝ)/3) := by
  have ht : eLpNorm f 2 μ^((1:ℝ)/3)*eLpNorm f 8 μ^((2:ℝ)/3)≠⊤ := by
    exact (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.eLpNorm_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h8.eLpNorm_ne_top)).ne
  have hh := (ENNReal.toReal_le_toReal (memLp_four h2 h8).eLpNorm_ne_top ht).mpr
    (eLpNorm_four_le h2.aestronglyMeasurable)
  simpa only [ENNReal.toReal_mul,←ENNReal.toReal_rpow,toReal_eLpNorm] using hh

theorem eLpNorm_four_tendsto_zero {l : Filter ι} {F : ι → α → E} {C : ℝ≥0∞}
    (hC : C≠⊤) (hF : ∀ᶠ i in l,AEStronglyMeasurable (F i) μ)
    (h8 : ∀ᶠ i in l,eLpNorm (F i) 8 μ≤C)
    (h2 : Tendsto (fun i => eLpNorm (F i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i) 4 μ) l (𝓝 0) := by
  have hr := (ENNReal.continuous_rpow_const (y:=(1:ℝ)/3)).tendsto 0 |>.comp h2
  have hc : C^((2:ℝ)/3)≠⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC
  have ht := ENNReal.Tendsto.mul_const hr (Or.inr hc)
  have hz : Tendsto (fun i => eLpNorm (F i) 2 μ^((1:ℝ)/3)*C^((2:ℝ)/3)) l (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.zero_rpow_of_pos (by norm_num : 0<(1:ℝ)/3),zero_mul] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hz (Eventually.of_forall (fun _ => (zero_le : (0:ℝ≥0∞)≤_)))
  filter_upwards [hF,h8] with i hf h8
  apply (eLpNorm_four_le hf).trans
  gcongr

end SphericalAging.LpEightInterpolation
