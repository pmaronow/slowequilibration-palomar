module

public import SphericalAging.LpMultiplierTruncation
public import Mathlib.MeasureTheory.Function.Holder

public section

/-! Genuine L² control of small linear plus quadratic pointwise remainders. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.LpQuadraticRemainder
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Ω E G : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedAddCommGroup G] {P : Measure Ω}

theorem normSquare_memLp {U : Ω → E} (hU : MemLp U 4 P) :
    MemLp (fun ω => ‖U ω‖^2) 2 P := by
  have hh := hU.norm_rpow_div (2 : ℝ≥0∞)
  norm_num [Real.rpow_two] at hh
  rw [show (4 : ℝ≥0∞)/2=2 by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]] at hh
  exact hh

theorem normSquare_lpNorm {U : Ω → E} (hU : MemLp U 4 P) :
    lpNorm (fun ω => ‖U ω‖^2) 2 P=(lpNorm U 4 P)^2 := by
  have hh := eLpNorm_norm_rpow U hU.aestronglyMeasurable (by norm_num : (0 : ℝ)<2)
    (p := (2 : ℝ≥0∞))
  norm_num [Real.rpow_two,ENNReal.rpow_two] at hh
  simpa only [toReal_eLpNorm,ENNReal.toReal_pow] using congrArg ENNReal.toReal hh

/-- A pointwise quadratic Taylor bound yields its actual L² norm bound. -/
theorem lpNorm_le_small_plus_square {U : Ω → E} {W : Ω → G}
    (hU2 : MemLp U 2 P) (hU4 : MemLp U 4 P) (hW : MemLp W 2 P)
    {ε C : ℝ} (hε : 0≤ε) (hC : 0≤C)
    (hb : ∀ᵐ ω ∂P,‖W ω‖≤ε*‖U ω‖+C*‖U ω‖^2) :
    lpNorm W 2 P≤ε*lpNorm U 2 P+C*(lpNorm U 4 P)^2 := by
  let B : Ω → ℝ := fun ω => ε*‖U ω‖+C*‖U ω‖^2
  have hB : MemLp B 2 P :=
    (hU2.norm.const_mul ε).add ((normSquare_memLp hU4).const_mul C)
  have he := eLpNorm_mono_ae_real (p := 2) hW.aestronglyMeasurable hb
  have hn : lpNorm W 2 P≤lpNorm B 2 P := by
    simpa only [toReal_eLpNorm] using
      (ENNReal.toReal_le_toReal hW.eLpNorm_ne_top hB.eLpNorm_ne_top).mpr he
  apply hn.trans
  have ht := lpNorm_add_le (hU2.norm.const_mul ε) (by norm_num : (1 : ℝ≥0∞)≤2)
    (g := fun ω => C*‖U ω‖^2)
  change lpNorm ((fun ω => ε*‖U ω‖)+(fun ω => C*‖U ω‖^2)) 2 P≤_
  simpa only [B,LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hε,
    abs_of_nonneg hC,LpMultiplierTruncation.lpNorm_norm hU2,normSquare_lpNorm hU4] using ht

end SphericalAging.LpQuadraticRemainder
