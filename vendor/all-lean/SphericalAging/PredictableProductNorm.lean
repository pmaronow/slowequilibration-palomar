module

public import SphericalAging.HessianQuadraticSource
public import Mathlib.MeasureTheory.Function.Holder

public section

/-! Hölder bounds for genuine square-integrable predictable products. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.PredictableProductNorm
open HardSphereDynamics LocalSDE
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

instance holderFourFourTwo : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
  change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹+((4 : ℝ≥0) : ℝ≥0∞)⁻¹=((2 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0)≠0),
    ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0)≠0),← ENNReal.coe_add]
  exact_mod_cast (by norm_num : (4 : ℝ≥0)⁻¹+(4 : ℝ≥0)⁻¹=(2 : ℝ≥0)⁻¹)⟩

theorem norm_le_of_product (R : PredictableProcessL2 F P)
    (U V : ℝ≥0 × Ω → State N) (hU : MemLp U 4 (nonnegativeLebesgueMeasure.prod P))
    (hV : MemLp V 4 (nonnegativeLebesgueMeasure.prod P)) (L : ℝ) (hL : 0≤L)
    (hbound : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(R : TimeProcessL2 P) q‖≤L*‖U q‖*‖V q‖) :
    ‖R‖≤L*(eLpNorm U 4 (nonnegativeLebesgueMeasure.prod P)).toReal*
      (eLpNorm V 4 (nonnegativeLebesgueMeasure.prod P)).toReal := by
  let μ := nonnegativeLebesgueMeasure.prod P
  have hh : eLpNorm (R : TimeProcessL2 P) 2 μ≤
      ENNReal.ofReal L*(eLpNorm U 4 μ*eLpNorm V 4 μ) := by
    calc
      _ ≤ ENNReal.ofReal L*eLpNorm (fun q => ‖U q‖*‖V q‖) 2 μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ) (c := L)
          (g := fun q => ‖U q‖*‖V q‖) (Lp.aestronglyMeasurable (R : TimeProcessL2 P))
          (hbound.mono (fun q hq => by
            rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
            simpa only [mul_assoc] using hq)) 2
      _ ≤ ENNReal.ofReal L*(eLpNorm U 4 μ*eLpNorm V 4 μ) := by
        apply mul_le_mul_right
        have hp := eLpNorm_smul_le_mul_eLpNorm (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞))
          (r := (2 : ℝ≥0∞)) hU.aestronglyMeasurable.norm hV.aestronglyMeasurable.norm
        rw [eLpNorm_norm U hU.aestronglyMeasurable,eLpNorm_norm V hV.aestronglyMeasurable] at hp
        change eLpNorm (fun q => ‖U q‖*‖V q‖) 2 μ≤eLpNorm U 4 μ*eLpNorm V 4 μ at hp
        exact hp
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  have hf : ENNReal.ofReal L*(eLpNorm U 4 μ*eLpNorm V 4 μ)≠∞ := by finiteness
  simpa only [μ,ENNReal.toReal_mul,ENNReal.toReal_ofReal hL,mul_assoc] using
    ENNReal.toReal_mono hf hh

end SphericalAging.PredictableProductNorm
