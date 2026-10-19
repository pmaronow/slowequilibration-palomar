module
public import FourPapersCommon.L2IntegralBounds

@[expose] public section

/-! Actual expectation bounds for bounded Lipschitz observables under an L²
coupling, including squared bounded observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_abs_le_sqrt_square (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ ω,|f ω| ∂P) ≤ Real.sqrt (∫ ω,(f ω)^2 ∂P) := by
  have hh := integral_sq_le_mass_mul_integral_sq (fun ω => ‖f ω‖) hf.norm
  simp only [probReal_univ,one_mul,Real.norm_eq_abs,sq_abs] at hh
  exact Real.le_sqrt_of_sq_le hh

theorem integral_observable_difference_le (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (f g : ℝ → ℝ) (hif : Integrable (fun ω => f (X ω)) P) (hig : Integrable (fun ω => g (Y ω)) P)
    {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hf : ∀ x,|f x-g x| ≤ ε) (hg : ∀ x y,|g x-g y| ≤ K*|x-y|) :
    |(∫ ω,f (X ω) ∂P)-(∫ ω,g (Y ω) ∂P)| ≤
      ε+K*Real.sqrt (∫ ω,(X ω-Y ω)^2 ∂P) := by
  have hd := hX.sub hY
  have hdi : Integrable (fun ω => |X ω-Y ω|) P := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hd.integrable (by norm_num)).norm
  have hm (ω : Ω) : |f (X ω)-g (Y ω)| ≤ ε+K*|X ω-Y ω| := by
    calc
      _ ≤ |f (X ω)-g (X ω)|+|g (X ω)-g (Y ω)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hf _) (hg _ _)
  calc
    _ = |∫ ω,f (X ω)-g (Y ω) ∂P| := by rw [integral_sub hif hig]
    _ ≤ ∫ ω,|f (X ω)-g (Y ω)| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => f (X ω)-g (Y ω))
    _ ≤ ∫ ω,ε+K*|X ω-Y ω| ∂P := integral_mono (hif.sub hig).norm
      ((integrable_const ε).add (hdi.const_mul K)) hm
    _ = ε+K*(∫ ω,|X ω-Y ω| ∂P) := by
      rw [integral_add (integrable_const ε) (hdi.const_mul K),integral_const,integral_const_mul]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_abs_le_sqrt_square (fun ω => X ω-Y ω) hd) hK)

theorem abs_square_sub_le_of_abs_le {a b C : ℝ} (hC : 0 ≤ C)
    (ha : |a| ≤ C) (hb : |b| ≤ C) : |a^2-b^2| ≤ 2*C*|a-b| := by
  have he : a^2-b^2 = (a-b)*(a+b) := by ring
  rw [he,abs_mul]
  calc
    _ ≤ |a-b| * (|a|+|b|) := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_add_le a b) (abs_nonneg _)
    _ ≤ |a-b| * (C+C) := mul_le_mul_of_nonneg_left (add_le_add ha hb) (abs_nonneg _)
    _ = _ := by ring

end FourPapersCommon
