module
public import FourPapersCommon.ScalarBrownianControl

@[expose] public section

/-! Linear combinations of actual adapted Brownian controls and their exact
terminal-state identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

theorem IsScalarBrownianControl.linearCombination {A B : ℝ → BrownianSample → ℝ}
    (hA : IsScalarBrownianControl A) (hB : IsScalarBrownianControl B) (a b : ℝ) :
    IsScalarBrownianControl (fun s sample=>a*A s sample+b*B s sample) := by
  obtain ⟨K,hK⟩ := hA.bounded
  obtain ⟨L,hL⟩ := hB.bounded
  refine ⟨fun sample=>(continuous_const.mul (hA.continuous_paths sample)).add
    (continuous_const.mul (hB.continuous_paths sample)),?_,?_,?_⟩
  · intro t
    exact ((hA.adapted t).const_mul a).add ((hB.adapted t).const_mul b)
  · exact (hA.measurable.const_mul a).add (hB.measurable.const_mul b)
  · refine ⟨⟨|a| *(K:ℝ)+|b| *(L:ℝ),by positivity⟩,?_⟩
    intro s sample
    change ‖a*A s sample+b*B s sample‖≤|a| *(K:ℝ)+|b| *(L:ℝ)
    calc
      _ ≤ ‖a*A s sample‖+‖b*B s sample‖ := norm_add_le _ _
      _ = |a| *‖A s sample‖+|b| *‖B s sample‖ := by simp only [norm_mul,Real.norm_eq_abs]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (hK s sample) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hL s sample) (abs_nonneg b))

theorem scalarControlledState_terminal_linearCombination
    (m m0 m1 x0 x1 a b c0 c1 : ℝ) (hab : a+b=1)
    (hc0 : m*c0=a*m0) (hc1 : m*c1=b*m1)
    (A B : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A)
    (hB : IsScalarBrownianControl B) (sample : BrownianSample) :
    scalarControlledState m (a*x0+b*x1) (fun s sample=>c0*A s sample+c1*B s sample) 1 sample=
      a*scalarControlledState m0 x0 A 1 sample+b*scalarControlledState m1 x1 B 1 sample := by
  simp_rw [scalarControlledState_terminal]
  have hadd := intervalIntegral.integral_add (μ:=volume)
    (((continuous_const : Continuous (fun _ : ℝ=>c0)).mul (hA.continuous_paths sample)).intervalIntegrable 0 1)
    (((continuous_const : Continuous (fun _ : ℝ=>c1)).mul (hB.continuous_paths sample)).intervalIntegrable 0 1)
  simp only [Pi.mul_apply] at hadd
  rw [hadd,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  linear_combination -(canonicalBrownian 1 sample)*hab+
    (∫ s in 0..(1 : ℝ),A s sample)*hc0+(∫ s in 0..(1 : ℝ),B s sample)*hc1

theorem scalarControlledState_terminal_sameControl
    (m0 m1 x0 x1 a b : ℝ) (hab : a+b=1) (A : ℝ → BrownianSample → ℝ)
    (sample : BrownianSample) :
    scalarControlledState (a*m0+b*m1) (a*x0+b*x1) A 1 sample=
      a*scalarControlledState m0 x0 A 1 sample+b*scalarControlledState m1 x1 A 1 sample := by
  simp_rw [scalarControlledState_terminal]
  linear_combination -(canonicalBrownian 1 sample)*hab

end FourPapersCommon
