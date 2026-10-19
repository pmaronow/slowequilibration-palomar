-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Genuine finite IID replica kernels. Each conditional law is the
ordinary finite product of the supplied Markov law. Prefix and pair
marginals are proved from independent product sampling, and remain exact
after an arbitrary disorder probability ensemble. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaKernel

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators Topology

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

def appendHead (n : ℕ) (p : V × (Fin n → V)) : Fin (n+1) → V := Fin.cons p.1 p.2

theorem appendHead_measurable (n : ℕ) : Measurable (appendHead (V := V) n) := by
  apply Measurable.of_eval
  intro j
  cases j using Fin.cases with
  | zero => exact measurable_fst
  | succ j => exact (measurable_pi_apply j).comp measurable_snd

/-- The actual finite product Markov kernel, built from ordinary products. -/
def iid (G : Kernel Ω V) : (n : ℕ) → Kernel Ω (Fin n → V)
  | 0 => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | n+1 => (G ×ₖ iid G n).map (appendHead n)

instance iid_markov (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) : IsMarkovKernel (iid G n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.deterministic _ _);infer_instance
  | succ n ih =>
    let _ : IsMarkovKernel (iid G n) := ih
    change IsMarkovKernel ((G ×ₖ iid G n).map (appendHead n))
    exact Kernel.IsMarkovKernel.map _ (appendHead_measurable n)

/-- Exact equality with the literal conditional finite-product measure. -/
theorem iid_apply (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) (ω : Ω) :
    iid G n ω=Measure.pi (fun _ : Fin n => G ω) := by
  induction n with
  | zero =>
    rw [iid,Kernel.deterministic_apply]
    exact (Measure.pi_of_empty _ Fin.elim0).symm
  | succ n ih =>
    rw [iid,Kernel.map_apply _ (appendHead_measurable n),Kernel.prod_apply,ih]
    change ((G ω).prod (Measure.pi (fun _ : Fin n => G ω))).map
      (fun p : V × (Fin n → V) => (Fin.cons p.1 p.2 : Fin (n+1) → V))=_
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => G ω) 0).symm.map_eq
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Equiv.coe_fn_mk,Fin.insertNth_zero,appendHead,cast_eq] using h

/-- The ordinary disorder-averaged finite-replica law. -/
def law (d : Measure Ω) (G : Kernel Ω V) (n : ℕ) : Measure (Fin n → V) := iid G n ∘ₘ d

instance law_probability (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) : IsProbabilityMeasure (law d G n) := by
  unfold law
  infer_instance

def initial {n : ℕ} (σ : Fin (n+1) → V) : Fin n → V := fun j => σ j.castSucc

theorem initial_measurable (n : ℕ) : Measurable (initial (V := V) (n := n)) :=
  Measurable.of_eval fun j => measurable_pi_apply j.castSucc

/-- Prefix marginal under the true conditional finite-product law. -/
theorem initial_pi_hasLaw (ν : Measure V) [IsProbabilityMeasure ν] (n : ℕ) :
    HasLaw (initial (V := V) (n := n)) (Measure.pi (fun _ : Fin n => ν))
      (Measure.pi (fun _ : Fin (n+1) => ν)) := by
  have h := (measurePreserving_snd (μ := ν) (ν := Measure.pi (fun _ : Fin n => ν))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n))
  have heq : (Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => V) (Fin.last n))=
      initial (V := V) (n := n) := by
    ext σ j
    simp [initial,MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv,Fin.init]
  rw [heq] at h
  exact h.hasLaw

/-- Prefix kernel identity derived from the conditional IID laws. -/
theorem iid_map_initial (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) :
    (iid G (n+1)).map initial=iid G n := by
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (initial_measurable n),iid_apply,iid_apply]
  exact (initial_pi_hasLaw (G ω) n).map_eq

/-- Prefix consistency after arbitrary ordinary disorder averaging. -/
theorem initial_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ) :
    HasLaw (initial (V := V) (n := n)) (law d G n) (law d G (n+1)) where
  aemeasurable := (initial_measurable n).aemeasurable
  map_eq := by rw [law,Measure.map_comp _ _ (initial_measurable n),iid_map_initial];rfl

/-- Distinct conditional replica coordinates have the actual product law. -/
theorem pair_pi_hasLaw (ν : Measure V) [IsProbabilityMeasure ν]
    {n : ℕ} (i j : Fin n) (hij : i≠j) :
    HasLaw (fun σ : Fin n → V => (σ i,σ j)) (ν.prod ν) (Measure.pi (fun _ : Fin n => ν)) := by
  have hi : iIndepFun (fun i (σ : Fin n → V) => σ i) (Measure.pi (fun _ : Fin n => ν)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact (hi.indepFun hij).hasLaw_prod (measurePreserving_eval (fun _ : Fin n => ν) i).hasLaw
    (measurePreserving_eval (fun _ : Fin n => ν) j).hasLaw

/-- Actual pair marginal kernel for any two distinct coordinates. -/
theorem iid_map_pair (G : Kernel Ω V) [IsMarkovKernel G] {n : ℕ}
    (i j : Fin n) (hij : i≠j) :
    (iid G n).map (fun σ => (σ i,σ j))=G ×ₖ G := by
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ ((measurable_pi_apply i).prodMk (measurable_pi_apply j)),
    iid_apply,Kernel.prod_apply]
  exact (pair_pi_hasLaw (G ω) i j hij).map_eq

/-- Disorder-averaged pair marginal, independent of the replica indices. -/
theorem pair_hasLaw (d : Measure Ω) (G : Kernel Ω V) [IsMarkovKernel G] {n : ℕ}
    (i j : Fin n) (hij : i≠j) :
    HasLaw (fun σ : Fin n → V => (σ i,σ j)) ((G ×ₖ G) ∘ₘ d) (law d G n) where
  aemeasurable := ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  map_eq := by
    rw [law,Measure.map_comp _ _ ((measurable_pi_apply i).prodMk (measurable_pi_apply j)),
      iid_map_pair G i j hij]

end SlowEquilibration.GaussianReplicaKernel
