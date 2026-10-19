module
public import OverlapPaper.BlockLaw
public import OverlapPaper.BlockPartition
public import OverlapPaper.PhysicalBounds
public import FourPapersCommon.GaussianSymmetry
public import Mathlib.Analysis.Subadditive

@[expose] public section

/-! Unconditional Guerra–Toninelli superadditivity and the mixed thermodynamic limit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace OverlapPaper
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem gaussian_freeEnergy_eq_physical {n : ℕ} (h : ℝ) (g : Disorder n) :
    SpinGlass.free_energy_density (N := n) (-g + SpinGlass.magnetic_field_vector n (-h)) =
      freeEnergy h g := by
  simp [SpinGlass.free_energy_density, SpinGlass.Z, SpinGlass.magnetic_field_vector,
    SpinGlass.magnetization, SpinGlass.spin, freeEnergy, partitionFunction, totalHamiltonian,
    hamiltonian, spin, div_eq_mul_inv, mul_comm, add_comm]

theorem integral_log_partitionFunction_eq {n : ℕ} (hn : 0 < n)
    (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    (∫ g : Disorder n, Real.log (partitionFunction h g) ∂disorderLaw ξ n) =
      (n : ℝ) * expectedFreeEnergy ξ h n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold expectedFreeEnergy freeEnergy
  rw [integral_div]
  field_simp

theorem integral_block_freeEnergy (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : ℝ) :
    (∫ g : Disorder (n + m), freeEnergy h g ∂blockDisorderLaw ξ n m) =
      ((n : ℝ) * expectedFreeEnergy ξ h n + (m : ℝ) * expectedFreeEnergy ξ h m) /
        ((n : ℝ) + (m : ℝ)) := by
  unfold blockDisorderLaw
  rw [integral_map_of_stronglyMeasurable (blockHamiltonianCLM n m).continuous.measurable
    (f := fun g : Disorder (n + m) => freeEnergy h g)
    (by
      unfold freeEnergy
      exact (((continuous_partitionFunction h).log
        (fun g => (partitionFunction_pos h g).ne')).div_const
          ((n + m : ℕ) : ℝ)).stronglyMeasurable)]
  simp only [blockHamiltonianCLM_apply, freeEnergy, integral_div]
  rw [integral_log_partitionFunction_block,
    integral_log_partitionFunction_eq hn, integral_log_partitionFunction_eq hm, Nat.cast_add]

theorem expectedLogPartition_superadditive_pos (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : ℝ) :
    (n : ℝ) * expectedFreeEnergy ξ h n + (m : ℝ) * expectedFreeEnergy ξ h m ≤
      ((n + m : ℕ) : ℝ) * expectedFreeEnergy ξ h (n + m) := by
  have hcomp := FourPapersCommon.gaussianMeasure_positive_freeEnergy_comparison
    (disorderLaw ξ (n + m)) (blockDisorderLaw ξ n m)
    (integral_disorder_eq_zero ξ (n + m)) (integral_blockDisorder_eq_zero ξ n m)
    (by
      intro σ
      rw [show (∫ g : Disorder (n + m), g σ * g σ ∂disorderLaw ξ (n + m)) =
        finiteCovariance ξ (n + m) σ σ from integral_hamiltonian_product ξ σ σ,
        integral_blockDisorder_product]
      exact finiteCovariance_blockCovariance_diag ξ hn hm σ)
    (by
      intro σ τ
      rw [show (∫ g : Disorder (n + m), g σ * g τ ∂disorderLaw ξ (n + m)) =
        finiteCovariance ξ (n + m) σ τ from integral_hamiltonian_product ξ σ τ,
        integral_blockDisorder_product]
      exact finiteCovariance_le_blockCovariance ξ hn hm σ τ)
    (SpinGlass.magnetic_field_vector (n + m) (-h))
  simp only [gaussian_freeEnergy_eq_physical] at hcomp
  rw [integral_block_freeEnergy ξ hn hm h] at hcomp
  change _ ≤ expectedFreeEnergy ξ h (n + m) at hcomp
  have hpos : 0 < (n : ℝ) + (m : ℝ) := by exact_mod_cast Nat.add_pos_left hn m
  rw [div_le_iff₀ hpos] at hcomp
  simpa only [Nat.cast_add, mul_comm] using hcomp

def physicalLogPressure (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * expectedFreeEnergy ξ h n

theorem physicalLogPressure_superadditive (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    ∀ n m, physicalLogPressure ξ h n + physicalLogPressure ξ h m ≤ physicalLogPressure ξ h (n + m) := by
  intro n m
  by_cases hn : n = 0
  · simp [hn, physicalLogPressure]
  by_cases hm : m = 0
  · simp [hm, physicalLogPressure]
  exact expectedLogPartition_superadditive_pos ξ (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm) h

theorem neg_physicalLogPressure_subadditive (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    Subadditive (fun n => -physicalLogPressure ξ h n) := by
  intro n m
  have hh := physicalLogPressure_superadditive ξ h n m
  linarith

def thermodynamicPressure (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) : ℝ :=
  -(neg_physicalLogPressure_subadditive ξ h).lim

theorem tendsto_expectedFreeEnergy (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    Tendsto (expectedFreeEnergy ξ h) atTop (𝓝 (thermodynamicPressure ξ h)) := by
  let u : ℕ → ℝ := fun n => -physicalLogPressure ξ h n
  have hu : Subadditive u := neg_physicalLogPressure_subadditive ξ h
  have hb : BddBelow (range (fun n : ℕ => u n / n)) := by
    refine ⟨min (-(Real.log 2 + |h| + ξ.value 1 / 2)) 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn, u, physicalLogPressure]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have he : u n / n = -expectedFreeEnergy ξ h n := by
      dsimp [u, physicalLogPressure]
      field_simp
    change min (-(Real.log 2 + |h| + ξ.value 1 / 2)) 0 ≤ u n / n
    rw [he]
    exact (min_le_left _ _).trans (neg_le_neg (expectedFreeEnergy_upper ξ (Nat.pos_of_ne_zero hn) h))
  have ht := (hu.tendsto_lim hb).neg
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  dsimp [u, physicalLogPressure]
  field_simp

end OverlapPaper
