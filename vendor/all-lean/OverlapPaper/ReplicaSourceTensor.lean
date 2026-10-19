module
public import OverlapPaper.ReplicaSourceTerminalLaw
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Finite tensor kernels, with exact normalization and marked-spin
expectation factorization. Unmarked coordinates remain genuine independent
coordinates in the law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators
namespace OverlapPaper
variable {A : Type*} [MeasurableSpace A]

def replicaPiKernel : (d : ℕ) → (Fin d → Kernel A ℝ) → Kernel A (Fin d → ℝ)
  | 0, _ => Kernel.deterministic (fun _ => (fun i : Fin 0 => Fin.elim0 i)) measurable_const
  | d + 1, Q => (Q 0 ×ₖ replicaPiKernel d (fun l => Q l.succ)).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm

theorem isMarkovKernel_replicaPiKernel (d : ℕ) (Q : Fin d → Kernel A ℝ)
    (hQ : ∀ l, IsMarkovKernel (Q l)) : IsMarkovKernel (replicaPiKernel d Q) := by
  induction d with
  | zero => change IsMarkovKernel (Kernel.deterministic _ _); infer_instance
  | succ d ih =>
    haveI := hQ 0
    haveI := ih (fun l => Q l.succ) (fun l => hQ l.succ)
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.measurable

theorem replicaPiKernel_apply (d : ℕ) (Q : Fin d → Kernel A ℝ)
    (hQ : ∀ l, IsMarkovKernel (Q l)) (x : A) :
    replicaPiKernel d Q x = Measure.pi (fun l => Q l x) := by
  induction d with
  | zero =>
    rw [replicaPiKernel, Kernel.deterministic_apply]
    exact (Measure.pi_of_empty _ _).symm
  | succ d ih =>
    haveI := hQ 0
    haveI := isMarkovKernel_replicaPiKernel d (fun l => Q l.succ) (fun l => hQ l.succ)
    haveI (l : Fin (d + 1)) : IsProbabilityMeasure (Q l x) := by haveI := hQ l; infer_instance
    rw [replicaPiKernel, Kernel.map_apply _ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.measurable,
      Kernel.prod_apply, ih (fun l => Q l.succ) (fun l => hQ l.succ)]
    simpa only [Fin.zero_succAbove] using
      (measurePreserving_piFinSuccAbove (fun l : Fin (d + 1) => Q l x) 0).symm.map_eq

theorem integral_replicaPiKernel_marked (d : ℕ) (Q : Fin d → Kernel A ℝ)
    (hQ : ∀ l, IsMarkovKernel (Q l)) (x : A) (J : Finset (Fin d)) :
    (∫ y, replicaTerminalCoefficient J y ∂replicaPiKernel d Q x) =
      ∏ l ∈ J, ∫ y, Real.tanh y ∂Q l x := by
  classical
  haveI (l : Fin d) : IsProbabilityMeasure (Q l x) := by haveI := hQ l; infer_instance
  rw [replicaPiKernel_apply d Q hQ x]
  have he (y : Fin d → ℝ) : replicaTerminalCoefficient J y =
      ∏ l : Fin d, if l ∈ J then Real.tanh (y l) else 1 := by
    simp only [replicaTerminalCoefficient, Finset.prod_ite_mem_eq]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun l y => if l ∈ J then Real.tanh y else (1 : ℝ))]
  have hl (l : Fin d) : (∫ y, (if l ∈ J then Real.tanh y else (1 : ℝ)) ∂Q l x) =
      if l ∈ J then (∫ y, Real.tanh y ∂Q l x) else 1 := by
    by_cases h : l ∈ J <;> simp [h]
  simp only [hl, Finset.prod_ite_mem_eq]

end OverlapPaper
