module
public import OverlapPaper.ReplicaProcess
public import OverlapPaper.MixedParisiFormula

@[expose] public section

/-! Literal finite-replica source partition functions.  The shell constrains
the actual physical replica overlaps.  Spins absent from a source monomial
remain in the counting sum.  The extended pressure is minus infinity for an
empty shell. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace OverlapPaper

abbrev ReplicaConfiguration (n d : ℕ) := Fin d → Configuration n

def replicaSpinProduct {d : ℕ} (J : Finset (Fin d)) (ε : Configuration d) : ℝ :=
  ∏ l ∈ J, spin (ε l)

theorem abs_replicaSpinProduct {d : ℕ} (J : Finset (Fin d)) (ε : Configuration d) :
    |replicaSpinProduct J ε| = 1 := by
  simp [replicaSpinProduct, Finset.abs_prod, abs_spin]

theorem replicaSpinProduct_sq {d : ℕ} (J : Finset (Fin d)) (ε : Configuration d) :
    replicaSpinProduct J ε ^ 2 = 1 := by
  rw [← sq_abs, abs_replicaSpinProduct]
  norm_num

def replicaSourceAverage {n d : ℕ} (J : Finset (Fin d)) (σ : ReplicaConfiguration n d) : ℝ :=
  (∑ i : Fin n, replicaSpinProduct J (fun l => σ l i)) / (n : ℝ)

theorem abs_replicaSourceAverage_le_one {n d : ℕ} (J : Finset (Fin d))
    (σ : ReplicaConfiguration n d) : |replicaSourceAverage J σ| ≤ 1 := by
  have H : |∑ i : Fin n, replicaSpinProduct J (fun l => σ l i)| ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ i : Fin n, |replicaSpinProduct J (fun l => σ l i)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_replicaSpinProduct, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
  by_cases hn : n = 0
  · simp [replicaSourceAverage, hn]
  · rw [replicaSourceAverage, abs_div]
    have hnabs : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
    rw [hnabs]
    exact (div_le_one (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr H

def replicaOverlapShell (n d : ℕ) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Finset (ReplicaConfiguration n d) := by
  classical
  exact Finset.univ.filter fun σ => ∀ l j : Fin d,
    l < j → |overlap (σ l) (σ j) - D l j| < η

theorem mem_replicaOverlapShell {n d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (σ : ReplicaConfiguration n d) :
    σ ∈ replicaOverlapShell n d D η ↔
      ∀ l j : Fin d, l < j → |overlap (σ l) (σ j) - D l j| < η := by
  classical
  simp [replicaOverlapShell]

def replicaSourceEnergy {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (g : Disorder n) (σ : ReplicaConfiguration n d) : ℝ :=
  (∑ l : Fin d, totalHamiltonian h g (σ l)) + θ * (n : ℝ) * replicaSourceAverage J σ

def replicaSourcePartition {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n) : ℝ :=
  ∑ σ ∈ replicaOverlapShell n d D η, Real.exp (replicaSourceEnergy h θ J g σ)

theorem replicaSourcePartition_nonneg {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n) :
    0 ≤ replicaSourcePartition h θ J D η g :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

theorem replicaSourcePartition_pos {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n)
    (hs : (replicaOverlapShell n d D η).Nonempty) :
    0 < replicaSourcePartition h θ J D η g :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hs

theorem replicaSourcePartition_eq_zero_iff {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n) :
    replicaSourcePartition h θ J D η g = 0 ↔ replicaOverlapShell n d D η = ∅ := by
  constructor
  · intro H
    by_contra hs
    exact (replicaSourcePartition_pos h θ J D η g (Finset.nonempty_iff_ne_empty.mpr hs)).ne' H
  · intro hs
    simp only [replicaSourcePartition, hs, Finset.sum_empty]

def replicaSourcePressureValue {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n) : ℝ :=
  Real.log (replicaSourcePartition h θ J D η g) / (n : ℝ)

def replicaSourcePressure {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n) : WithBot ℝ :=
  if replicaOverlapShell n d D η = ∅ then ⊥
    else ↑(replicaSourcePressureValue h θ J D η g)

theorem replicaSourcePressure_empty {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n)
    (hs : replicaOverlapShell n d D η = ∅) : replicaSourcePressure h θ J D η g = ⊥ := by
  simp only [replicaSourcePressure, hs, ite_true]

theorem replicaSourcePressure_nonempty {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (g : Disorder n)
    (hs : (replicaOverlapShell n d D η).Nonempty) :
    replicaSourcePressure h θ J D η g = ↑(replicaSourcePressureValue h θ J D η g) := by
  simp only [replicaSourcePressure, Finset.Nonempty.ne_empty hs, ite_false]

def replicaSourceTerminal {d : ℕ} (J : Finset (Fin d)) (θ : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.log (∑ ε : Configuration d,
    Real.exp ((∑ l : Fin d, x l * spin (ε l)) + θ * replicaSpinProduct J ε))

end OverlapPaper
