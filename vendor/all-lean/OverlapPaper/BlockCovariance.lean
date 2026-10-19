module
public import OverlapPaper.FiniteModel
public import FourPapersCommon.MixtureConvexity
public import ParisiFormula.GuerraToninelli

@[expose] public section

/-! Exact block covariances for the mixed physical Hamiltonian. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OverlapPaper
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

def blockHamiltonian {n m : ℕ} (g : Disorder n × Disorder m) : Disorder (n + m) :=
  WithLp.toLp 2 (fun σ : Configuration (n + m) =>
    g.1 (SpinGlass.cfgLeft (N := n) (M := m) σ) +
      g.2 (SpinGlass.cfgRight (N := n) (M := m) σ))

def blockHamiltonianCLM (n m : ℕ) : Disorder n × Disorder m →L[ℝ] Disorder (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := blockHamiltonian
      map_add' := by intro g z; ext σ; simp [blockHamiltonian]; ring
      map_smul' := by intro c g; ext σ; simp [blockHamiltonian]; ring }

@[simp] theorem blockHamiltonianCLM_apply (n m : ℕ) (g : Disorder n × Disorder m) :
    blockHamiltonianCLM n m g = blockHamiltonian g := rfl

theorem overlap_split {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (σ τ : Configuration (n + m)) :
    overlap σ τ =
      ((n : ℝ) * overlap (SpinGlass.cfgLeft (N := n) (M := m) σ)
        (SpinGlass.cfgLeft (N := n) (M := m) τ) +
       (m : ℝ) * overlap (SpinGlass.cfgRight (N := n) (M := m) σ)
        (SpinGlass.cfgRight (N := n) (M := m) τ)) / ((n : ℝ) + (m : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnm0 : (n : ℝ) + (m : ℝ) ≠ 0 := by positivity
  simp only [overlap, SpinGlass.cfgLeft, SpinGlass.cfgRight, Nat.cast_add, Fin.sum_univ_add]
  field_simp

def blockCovariance (ξ : FourPapersCommon.AdmissibleEvenMixture) (n m : ℕ)
    (σ τ : Configuration (n + m)) : ℝ :=
  finiteCovariance ξ n (SpinGlass.cfgLeft (N := n) (M := m) σ)
    (SpinGlass.cfgLeft (N := n) (M := m) τ) +
  finiteCovariance ξ m (SpinGlass.cfgRight (N := n) (M := m) σ)
    (SpinGlass.cfgRight (N := n) (M := m) τ)

theorem finiteCovariance_le_blockCovariance (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (σ τ : Configuration (n + m)) :
    finiteCovariance ξ (n + m) σ τ ≤ blockCovariance ξ n m σ τ := by
  unfold finiteCovariance blockCovariance
  rw [overlap_split hn hm, Nat.cast_add]
  exact ξ.convex_covariance_block_bound (overlap_mem_unit _ _) (overlap_mem_unit _ _)
    (n : ℝ) (m : ℝ) (by exact_mod_cast hn) (by exact_mod_cast hm)

theorem finiteCovariance_blockCovariance_diag (ξ : FourPapersCommon.AdmissibleEvenMixture)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (σ : Configuration (n + m)) :
    finiteCovariance ξ (n + m) σ σ = blockCovariance ξ n m σ σ := by
  simp [finiteCovariance, blockCovariance, overlap_self hn, overlap_self hm,
    overlap_self (Nat.add_pos_left hn m), Nat.cast_add, add_mul]

end OverlapPaper
