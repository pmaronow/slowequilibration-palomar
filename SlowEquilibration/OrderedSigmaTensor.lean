-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic

/-! Degree patterns and unrestricted ordered tensor slots. These bijections
retain repeated indices and diagonal coordinates. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.OrderedSigmaTensor
open scoped BigOperators
set_option autoImplicit false

def degreeBlocksEquiv {κ P : Type*} (T : P → Type*) :
    (κ → Sigma T) ≃ Sigma (fun p : κ → P => ∀ j, T (p j)) where
  toFun I := ⟨fun j => (I j).1, fun j => (I j).2⟩
  invFun I := fun j => ⟨I.1 j, I.2 j⟩
  left_inv I := by funext j; rfl
  right_inv I := by cases I; rfl

/-- An ordered coordinate sum is a finite sum of fixed physical-degree
blocks. The number of degree blocks is independent of tensor dimension. -/
theorem sum_degree_blocks {κ P : Type*} [Fintype κ] [DecidableEq κ] [Fintype P]
    (T : P → Type*) [∀ p, Fintype (T p)] (f : (κ → Sigma T) → ℝ) :
    (∑ I, f I) = ∑ p : κ → P, ∑ I : ∀ j, T (p j), f (fun j => ⟨p j, I j⟩) := by
  classical
  calc
    _ = ∑ I : Sigma (fun p : κ → P => ∀ j, T (p j)), f (fun j => ⟨I.1 j, I.2 j⟩) :=
      Fintype.sum_equiv (degreeBlocksEquiv T) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

/-- Flatten every slot of every ordered tensor, including all repetitions. -/
def tensorSlotsEquiv {k : ℕ} (p : Fin k → ℕ) (ι : Type*) :
    (∀ j, Fin (p j) → ι) ≃ (Fin (∑ j, p j) → ι) where
  toFun I b := I ((finSigmaFinEquiv (n := p)).symm b).1 ((finSigmaFinEquiv (n := p)).symm b).2
  invFun I j a := I (finSigmaFinEquiv (n := p) ⟨j, a⟩)
  left_inv I := by
    funext j a
    exact congrArg (fun ja : (j : Fin k) × Fin (p j) => I ja.1 ja.2)
      ((finSigmaFinEquiv (n := p)).symm_apply_apply ⟨j, a⟩)
  right_inv I := by
    funext b
    exact congrArg I ((finSigmaFinEquiv (n := p)).apply_symm_apply b)

@[simp] theorem tensorSlotsEquiv_apply_block {k : ℕ} (p : Fin k → ℕ) {ι : Type*}
    (I : ∀ j, Fin (p j) → ι) (j : Fin k) (a : Fin (p j)) :
    tensorSlotsEquiv p ι I (finSigmaFinEquiv (n := p) ⟨j, a⟩) = I j a := by
  exact congrArg (fun ja : (j : Fin k) × Fin (p j) => I ja.1 ja.2)
    ((finSigmaFinEquiv (n := p)).symm_apply_apply ⟨j, a⟩)

def flatLabels {k : ℕ} {κ : Type*} (p : Fin k → ℕ) (labels : Fin k → κ) :
    Fin (∑ j, p j) → κ := fun b => labels ((finSigmaFinEquiv (n := p)).symm b).1

theorem prod_tensor_slots {k : ℕ} {κ ι : Type*} (p : Fin k → ℕ)
    (labels : Fin k → κ) (σ : κ → ι → ℝ) (I : ∀ j, Fin (p j) → ι) :
    (∏ j, ∏ a, σ (labels j) (I j a)) =
      ∏ b, σ (flatLabels p labels b) (tensorSlotsEquiv p ι I b) := by
  classical
  calc
    _ = ∏ ja : (j : Fin k) × Fin (p j), σ (labels ja.1) (I ja.1 ja.2) :=
      (Fintype.prod_sigma _).symm
    _ = _ := Fintype.prod_equiv (finSigmaFinEquiv (n := p)) _ _ (fun ja => by
      exact (congrArg (fun ja : (j : Fin k) × Fin (p j) =>
        σ (labels ja.1) (I ja.1 ja.2))
        ((finSigmaFinEquiv (n := p)).symm_apply_apply ja)).symm)

theorem sum_tensor_slots {k : ℕ} (p : Fin k → ℕ) (ι : Type*) [Fintype ι]
    (f : (∀ j, Fin (p j) → ι) → ℝ) :
    (∑ I, f I) = ∑ I : Fin (∑ j, p j) → ι, f ((tensorSlotsEquiv p ι).symm I) := by
  classical
  exact Fintype.sum_equiv (tensorSlotsEquiv p ι) _ _ (fun I => by simp)

end SlowEquilibration.OrderedSigmaTensor
