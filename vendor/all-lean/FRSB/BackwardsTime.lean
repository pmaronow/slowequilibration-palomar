module
public import FRSB.BackwardsDefinitions
public import FRSB.BackwardsEvolutionJets
public import FRSB.FiniteTimeHierarchy

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace FRSB

theorem backwardD_eq_spatialJet (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) (t x : ℝ) :
    backwardD β μ j (t, x) = parisiSpatialJet β μ j t x := by
  cases j with
  | zero => simp [backwardD, Paper.parisiSpatialField, parisiSpatialJet]
  | succ j => simp [backwardD, Paper.parisiSpatialField, parisiSpatialJet]

def backwardTime (β τ : ℝ) : ℝ := 1 - τ / β ^ 2
def backwardTauD (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  backwardD β μ j (backwardTime β p.1, p.2)

def backwardTauForcing (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  (backwardTauD β μ (j + 2) p + a * ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * backwardTauD β μ (i + 1) p * backwardTauD β μ (j - i + 1) p) / 2

def backwardCellStart {k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β : ℝ) (p : ℕ) : ℝ :=
  β ^ 2 * (1 - s.q (p + 1))
def backwardCellEnd {k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β : ℝ) (p : ℕ) : ℝ :=
  β ^ 2 * (1 - s.q p)

theorem backwardTime_cell_mem {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (p : ℕ) (τ : ℝ)
    (hτ : τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p)) :
    backwardTime β τ ∈ Icc (s.q p) (s.q (p + 1)) := by
  have hsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hlo : 1 - s.q (p + 1) ≤ τ / β ^ 2 := (le_div_iff₀ hsq).mpr (by
    simpa only [backwardCellStart, mul_comm] using hτ.1)
  have hhi : τ / β ^ 2 ≤ 1 - s.q p := (div_le_iff₀ hsq).mpr (by
    simpa only [backwardCellEnd, mul_comm] using hτ.2)
  dsimp [backwardTime]
  constructor <;> linarith

theorem backwardTime_cell_mem_interior {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (p : ℕ) (τ : ℝ)
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) :
    backwardTime β τ ∈ Ioo (s.q p) (s.q (p + 1)) := by
  have hsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hlo : 1 - s.q (p + 1) < τ / β ^ 2 := (lt_div_iff₀ hsq).mpr (by
    simpa only [backwardCellStart, mul_comm] using hτ.1)
  have hhi : τ / β ^ 2 < 1 - s.q p := (div_lt_iff₀ hsq).mpr (by
    simpa only [backwardCellEnd, mul_comm] using hτ.2)
  dsimp [backwardTime]
  constructor <;> linarith

theorem hasDerivAt_backwardTime (β τ : ℝ) :
    HasDerivAt (backwardTime β) (-(1 / β ^ 2)) τ := by
  convert (hasDerivAt_const τ (1 : ℝ)).sub ((hasDerivAt_id τ).div_const (β ^ 2)) using 1
  · funext r
    rfl
  · simp only [zero_sub]

/-- The genuine all-order hierarchy in the paper's backward time. -/
theorem hasDerivAt_finiteCell_backwardTauD {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardTauD β (Paper.parisiSchemeMeasure s) j (r, x))
      (backwardTauForcing β (Paper.parisiSchemeMeasure s) (s.m p) j (τ, x)) τ := by
  have ht := backwardTime_cell_mem_interior s β hβ p τ hτ
  have hd := (hasDerivAt_finiteCell_spatialJet_time s β hβ hp hq j ht x).comp τ
    (hasDerivAt_backwardTime β τ)
  convert hd using 1
  · funext r
    exact backwardD_eq_spatialJet β (Paper.parisiSchemeMeasure s) j (backwardTime β r) x
  · rw [cellTimeForcing_eq]
    simp only [backwardTauForcing, backwardTauD, backwardD_eq_spatialJet]
    field_simp

theorem backwardTauForcing_one (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) :
    backwardTauForcing β μ a 1 p =
      backwardTauD β μ 3 p / 2 + a * backwardTauD β μ 1 p * backwardTauD β μ 2 p := by
  simp [backwardTauForcing, Finset.sum_range_succ]
  ring

theorem backwardTauForcing_two (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) :
    backwardTauForcing β μ a 2 p = backwardCtJet a (backwardTauD β μ 1 p)
      (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p) := by
  norm_num [backwardTauForcing, backwardCtJet, Finset.sum_range_succ]
  ring

theorem backwardTauForcing_three (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) :
    backwardTauForcing β μ a 3 p = backwardDtJet a (backwardTauD β μ 1 p)
      (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p) (backwardTauD β μ 5 p) := by
  norm_num [backwardTauForcing, backwardDtJet, Finset.sum_range_succ]
  ring

theorem backwardTauForcing_four (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) :
    backwardTauForcing β μ a 4 p = backwardEtJet a (backwardTauD β μ 1 p)
      (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p)
      (backwardTauD β μ 5 p) (backwardTauD β μ 6 p) := by
  norm_num [backwardTauForcing, backwardEtJet, Finset.sum_range_succ, Nat.choose]
  ring

theorem backwardTauForcing_five (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) :
    backwardTauForcing β μ a 5 p = backwardFtJet a (backwardTauD β μ 1 p)
      (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p)
      (backwardTauD β μ 5 p) (backwardTauD β μ 6 p) (backwardTauD β μ 7 p) := by
  norm_num [backwardTauForcing, backwardFtJet, Finset.sum_range_succ, Nat.choose]
  ring

end FRSB
