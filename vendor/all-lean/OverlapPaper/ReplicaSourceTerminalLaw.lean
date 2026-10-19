module
public import OverlapPaper.ReplicaSourceTerminal
public import OverlapPaper.ReplicaSourceHoeffding
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

/-! The terminal source estimate integrated against an actual probability
law of the branching fields, with its literal marked-magnetization coefficient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators
namespace OverlapPaper

theorem log_cosh_add_mul_sinh_le (c θ : ℝ) (hc : |c| ≤ 1) :
    Real.log (Real.cosh θ + c * Real.sinh θ) ≤ θ * c + θ ^ 2 / 2 := by
  let p : unitInterval := ⟨(c + 1) / 2, by constructor <;> linarith [abs_le.mp hc]⟩
  let μ := bernoulliMeasure true false p
  have H := source_log_mgf_le μ spin (measurable_of_countable spin).aemeasurable
    (Filter.Eventually.of_forall (fun b => (abs_spin b).le)) θ
  have hm : (∫ b, spin b ∂μ) = c := by
    rw [show μ = bernoulliMeasure true false p from rfl, integral_bernoulliMeasure]
    simp [spin, p]
    ring
  have he : (∫ b, Real.exp (θ * spin b) ∂μ) = Real.cosh θ + c * Real.sinh θ := by
    rw [show μ = bernoulliMeasure true false p from rfl, integral_bernoulliMeasure]
    simp [spin, p, Real.cosh_eq, Real.sinh_eq]
    ring
  rwa [hm, he] at H

def replicaTerminalCoefficient {d : ℕ} (J : Finset (Fin d)) (x : Fin d → ℝ) : ℝ :=
  ∏ l ∈ J, Real.tanh (x l)

theorem abs_replicaTerminalCoefficient_le_one {d : ℕ} (J : Finset (Fin d))
    (x : Fin d → ℝ) : |replicaTerminalCoefficient J x| ≤ 1 := by
  rw [replicaTerminalCoefficient, Finset.abs_prod]
  calc
    _ ≤ ∏ l ∈ J, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun l _ => (Real.abs_tanh_lt_one (x l)).le)
    _ = _ := by simp

theorem continuous_replicaTerminalCoefficient {d : ℕ} (J : Finset (Fin d)) :
    Continuous (replicaTerminalCoefficient J) := by
  unfold replicaTerminalCoefficient
  fun_prop

theorem integrable_replicaTerminalCoefficient {d : ℕ} (J : Finset (Fin d))
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (replicaTerminalCoefficient J) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (continuous_replicaTerminalCoefficient J).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_replicaTerminalCoefficient_le_one J x

theorem source_terminal_law_bound {d : ℕ} (J : Finset (Fin d))
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (θ : ℝ) :
    Real.log (∫ x, Real.exp (replicaSourceTerminal J θ x - replicaSourceTerminal J 0 x) ∂μ)
      ≤ θ * (∫ x, replicaTerminalCoefficient J x ∂μ) + θ ^ 2 / 2 := by
  have hi := integrable_replicaTerminalCoefficient J μ
  have he : (∫ x, Real.exp (replicaSourceTerminal J θ x - replicaSourceTerminal J 0 x) ∂μ) =
      Real.cosh θ + (∫ x, replicaTerminalCoefficient J x ∂μ) * Real.sinh θ := by
    simp_rw [replicaSourceTerminal_ratio]
    change (∫ x, Real.cosh θ + replicaTerminalCoefficient J x * Real.sinh θ ∂μ) = _
    rw [integral_add (integrable_const _) (hi.mul_const _), integral_const, integral_mul_const]
    simp [replicaTerminalCoefficient]
  rw [he]
  apply log_cosh_add_mul_sinh_le
  calc
    |∫ x, replicaTerminalCoefficient J x ∂μ| ≤ ∫ x, |replicaTerminalCoefficient J x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 : ℝ) ∂μ := integral_mono hi.abs (integrable_const _) (fun x => abs_replicaTerminalCoefficient_le_one J x)
    _ = 1 := by simp

end OverlapPaper
