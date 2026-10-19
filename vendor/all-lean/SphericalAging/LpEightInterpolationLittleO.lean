module

public import SphericalAging.LpEightInterpolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section
/-! True fourth-norm little-o follows from second-norm little-o and
eighth-norm big-O, on arbitrary measures and filters. -/
noncomputable section
open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal
namespace SphericalAging.LpEightInterpolationLittleO
variable {α E V ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedAddCommGroup V] {μ : Measure α} {l : Filter ι}

theorem lpNorm_four_isLittleO {R : ι → α → E} {g : ι → V}
    (h2 : ∀ᶠ i in l,MemLp (R i) 2 μ) (h8 : ∀ᶠ i in l,MemLp (R i) 8 μ)
    (hsmall : (fun i => lpNorm (R i) 2 μ)=o[l] g)
    (hbounded : (fun i => lpNorm (R i) 8 μ)=O[l] g) :
    (fun i => lpNorm (R i) 4 μ)=o[l] g := by
  have hpos : ∀ᶠ i in l,0≤‖g i‖ := .of_forall (fun _ => norm_nonneg _)
  have ha := hsmall.norm_right.rpow (r := (1 : ℝ)/3) (by norm_num) hpos
  have hb := hbounded.norm_right.rpow (r := (2 : ℝ)/3) (by norm_num) hpos
  have hp := ha.mul_isBigO hb
  have he (i : ι) : ‖g i‖^((1 : ℝ)/3)*‖g i‖^((2 : ℝ)/3)=‖g i‖ := by
    rw [←Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ)≤1/3) (by norm_num : (0 : ℝ)≤2/3)]
    norm_num
  have hp' : (fun i => lpNorm (R i) 2 μ^((1 : ℝ)/3)*lpNorm (R i) 8 μ^((2 : ℝ)/3))=o[l] g := by
    apply IsLittleO.of_norm_right
    exact hp.congr_right he
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [h2,h8,hp'.bound hε] with i h2i h8i hi
  rw [Real.norm_of_nonneg lpNorm_nonneg]
  apply (LpEightInterpolation.lpNorm_four_le h2i h8i).trans
  exact (le_abs_self _).trans hi
end SphericalAging.LpEightInterpolationLittleO
