module

public import SphericalAging.LpMomentBounds
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public section
/-! Moment algebra for the actual representatives of L² classes. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SphericalAging.LpClassMomentAlgebra
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} {q : ℝ≥0∞}
theorem memLp_sub_coe (U V : Lp E 2 μ) (hU : MemLp (U : Ω → E) q μ)
    (hV : MemLp (V : Ω → E) q μ) : MemLp (U-V : Lp E 2 μ) q μ :=
  (hU.sub hV).ae_eq (Lp.coeFn_sub U V).symm
theorem lpNorm_sub_coe_le (U V : Lp E 2 μ) (hU : MemLp (U : Ω → E) q μ) (hq : 1≤q) :
    lpNorm (U-V : Lp E 2 μ) q μ≤lpNorm (U : Ω → E) q μ+lpNorm (V : Ω → E) q μ := by
  have he : lpNorm (U-V : Lp E 2 μ) q μ=lpNorm ((U : Ω → E)-(V : Ω → E)) q μ :=
    congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub U V))
  rw [he]
  exact lpNorm_sub_le hU hq
theorem lpNorm_two_coe (U : Lp E 2 μ) : lpNorm (U : Ω → E) 2 μ=‖U‖ :=
  (Lp.norm_def U).symm
end SphericalAging.LpClassMomentAlgebra
