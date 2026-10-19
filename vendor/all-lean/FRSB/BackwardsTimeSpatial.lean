module
public import FRSB.BackwardsTime
public import FRSB.UniformSpatialRegularity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem backwardTime_mem (β : ℝ) (hβ : β ≠ 0) (τ : ℝ)
    (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) : backwardTime β τ ∈ Icc (0 : ℝ) 1 := by
  have hsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hdiv0 : 0 ≤ τ / β ^ 2 := div_nonneg hτ.1 hsq.le
  have hdiv1 : τ / β ^ 2 ≤ 1 := (div_le_iff₀ hsq).mpr (by simpa using hτ.2)
  dsimp [backwardTime]
  constructor <;> linarith

theorem continuous_backwardTauD (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) :
    Continuous (backwardTauD β μ j) :=
  (Paper.continuous_parisiSpatialField β μ j).comp
    ((by unfold backwardTime; fun_prop : Continuous (fun p : ℝ × ℝ => backwardTime β p.1)).prodMk continuous_snd)

theorem backwardTauD_uniform_bound (β : ℝ) (μ : Paper.ParisiMeasure) (j : ℕ) (p : ℝ × ℝ) :
    |backwardTauD β μ (j + 1) p| ≤ uniformSpatialConstant β j := by
  simpa only [Real.norm_eq_abs, backwardTauD, backwardD] using
    parisiSpatialField_uniform_bound β j μ (backwardTime β p.1, p.2)

theorem hasDerivAt_backwardTauD_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (j : ℕ) (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauD β μ j (τ, y)) (backwardTauD β μ (j + 1) (τ, x)) x :=
  hasDerivAt_backwardD β μ j (backwardTime β τ) x (backwardTime_mem β hβ τ hτ)

theorem deriv_backwardTauD_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (j : ℕ) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    deriv (fun y => backwardTauD β μ j (τ, y)) = fun y => backwardTauD β μ (j + 1) (τ, y) :=
  funext fun y => (hasDerivAt_backwardTauD_spatial β hβ μ j τ y hτ).deriv

theorem deriv2_backwardTauD_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (j : ℕ) (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    deriv (deriv (fun y => backwardTauD β μ j (τ, y))) x = backwardTauD β μ (j + 2) (τ, x) := by
  rw [deriv_backwardTauD_spatial β hβ μ j τ hτ]
  exact (hasDerivAt_backwardTauD_spatial β hβ μ (j + 1) τ x hτ).deriv

theorem backwardTauC_pos_le_one (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    0 < backwardTauD β μ 2 (τ, x) ∧ backwardTauD β μ 2 (τ, x) ≤ 1 :=
  ⟨backwardC_pos β hβ μ (backwardTime β τ) x (backwardTime_mem β hβ τ hτ),
    backwardC_le_one β hβ μ (backwardTime β τ) x (backwardTime_mem β hβ τ hτ)⟩

theorem backwardTauB_abs_le_one (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) : |backwardTauD β μ 1 (τ, x)| ≤ 1 := by
  rw [show backwardTauD β μ 1 (τ, x) = backwardB β μ (backwardTime β τ, x) by rfl,
    backwardB_eq_gradient β μ (backwardTime β τ) x (backwardTime_mem β hβ τ hτ)]
  simpa only [Real.norm_eq_abs] using Paper.norm_parisiGradient_le_one β μ (backwardTime β τ, x)

end FRSB
