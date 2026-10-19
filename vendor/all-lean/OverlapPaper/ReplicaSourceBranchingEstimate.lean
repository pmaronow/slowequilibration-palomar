module
public import OverlapPaper.ReplicaSourceMarkovRecursion
public import OverlapPaper.ReplicaSourceTerminalBound
public import OverlapPaper.ReplicaSourceTerminalLaw
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Finite normalized branching laws and the closed marked-source estimate
for their actual logarithmic recursion. Kernels are composed in the backward
recursion order, so the last displayed kernel is the first physical step. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace OverlapPaper
variable {A : Type*} [MeasurableSpace A]

def sourceKernelLaw (Q : ℕ → Kernel A A) : ℕ → Kernel A A
  | 0 => Kernel.id
  | k + 1 => sourceKernelLaw Q k ∘ₖ Q k

theorem isMarkovKernel_sourceKernelLaw (Q : ℕ → Kernel A A)
    (hQ : ∀ j, IsMarkovKernel (Q j)) (k : ℕ) : IsMarkovKernel (sourceKernelLaw Q k) := by
  induction k with
  | zero => exact Kernel.instIsMarkovKernelId
  | succ k ih =>
    haveI := ih
    haveI := hQ k
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

theorem sourceKernelExpectation_eq_integral (Q : ℕ → Kernel A A)
    (hQ : ∀ j, IsMarkovKernel (Q j)) (w : A → ℝ) (hw : Measurable w)
    (K : ℝ) (hb : ∀ x, |w x| ≤ K) (k : ℕ) (x : A) :
    sourceKernelExpectation Q k w x = ∫ y, w y ∂sourceKernelLaw Q k x := by
  induction k generalizing x with
  | zero => rw [sourceKernelExpectation, sourceKernelLaw, Kernel.id_apply, integral_dirac' w x hw.stronglyMeasurable]
  | succ k ih =>
    haveI := isMarkovKernel_sourceKernelLaw Q hQ k
    haveI := hQ k
    change (∫ y, sourceKernelExpectation Q k w y ∂Q k x) = ∫ y, w y ∂(sourceKernelLaw Q k ∘ₖ Q k) x
    rw [Kernel.integral_comp (source_bounded_integrable _ w hw K hb)]
    simp_rw [ih]

theorem sourceKernelRecursion_le_log_terminal_expectation
    (Q : ℕ → Kernel A A) (hQ : ∀ j, IsMarkovKernel (Q j))
    (a : ℕ → ℝ) (ha : ∀ j, a j ∈ Icc 0 1) (w : A → ℝ) (hw : Measurable w)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |w x| ≤ K) (k : ℕ) (x : A) :
    sourceKernelRecursion Q a k w x ≤ Real.log (∫ y, Real.exp (w y) ∂sourceKernelLaw Q k x) := by
  have H := sourceKernelRecursion_exponential_domination Q hQ a ha w hw K hK hb k x
  have hem : Measurable (fun y => Real.exp (w y)) := measurable_exp.comp hw
  have heb (y : A) : |Real.exp (w y)| ≤ Real.exp K := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb y))
  rw [sourceKernelExpectation_eq_integral Q hQ _ hem (Real.exp K) heb k x] at H
  have Hlog := Real.log_le_log (Real.exp_pos _) H
  simpa only [Real.log_exp] using Hlog

theorem source_branching_terminal_estimate {d : ℕ}
    (Q : ℕ → Kernel (Fin d → ℝ) (Fin d → ℝ)) (hQ : ∀ j, IsMarkovKernel (Q j))
    (a : ℕ → ℝ) (ha : ∀ j, a j ∈ Icc 0 1) (J : Finset (Fin d))
    (θ : ℝ) (k : ℕ) (x : Fin d → ℝ) :
    sourceKernelRecursion Q a k
      (fun y => replicaSourceTerminal J θ y - replicaSourceTerminal J 0 y) x ≤
        θ * (∫ y, replicaTerminalCoefficient J y ∂sourceKernelLaw Q k x) + θ ^ 2 / 2 := by
  haveI := isMarkovKernel_sourceKernelLaw Q hQ k
  have hm : Measurable (fun y => replicaSourceTerminal J θ y - replicaSourceTerminal J 0 y) := by
    unfold replicaSourceTerminal
    fun_prop
  exact (sourceKernelRecursion_le_log_terminal_expectation Q hQ a ha _ hm |θ| (abs_nonneg θ)
    (fun y => abs_replicaSourceTerminal_sub_le J θ y) k x).trans
      (source_terminal_law_bound J (sourceKernelLaw Q k x) θ)

end OverlapPaper
