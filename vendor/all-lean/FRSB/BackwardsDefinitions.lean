module
public import FRSB.BackwardsJets

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem hasDerivAt_backwardD (β : ℝ) (μ : Paper.ParisiMeasure) (n : ℕ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardD β μ n (t, y)) (backwardD β μ (n + 1) (t, x)) x :=
  Paper.hasDerivAt_parisiSpatialField β μ n t x ht

/-- The literal logarithmic curvature derivative of the actual potential. -/
theorem backwardZ_eq_logarithmicCurvature (β : ℝ) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardZ β μ (t, x) = -deriv (fun y => backwardC β μ (t, y)) x /
      (2 * backwardC β μ (t, x)) := by
  change -backwardD β μ 3 (t, x) / (2 * backwardC β μ (t, x)) =
    -deriv (fun y => backwardD β μ 2 (t, y)) x / (2 * backwardC β μ (t, x))
  rw [(hasDerivAt_backwardD β μ 2 t x ht).deriv]

theorem hasDerivAt_backwardZ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardZ β μ (t, y)) (backwardZx β μ (t, x)) x := by
  have hC : backwardC β μ (t, x) ≠ 0 := (backwardC_pos β hβ μ t x ht).ne'
  have hh := (hasDerivAt_backwardD β μ 3 t x ht).neg.div
    ((hasDerivAt_backwardD β μ 2 t x ht).const_mul 2) (mul_ne_zero (by norm_num) hC)
  convert hh using 1
  · funext y
    rfl
  · dsimp [backwardZx, backwardZxJet, backwardC] at *
    field_simp
    ring

theorem hasDerivAt_backwardZx (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardZx β μ (t, y)) (backwardZxx β μ (t, x)) x := by
  have hC : backwardC β μ (t, x) ≠ 0 := (backwardC_pos β hβ μ t x ht).ne'
  have h1 := (hasDerivAt_backwardD β μ 4 t x ht).neg.div
    ((hasDerivAt_backwardD β μ 2 t x ht).const_mul 2) (mul_ne_zero (by norm_num) hC)
  have h2 := ((hasDerivAt_backwardD β μ 3 t x ht).pow 2).div
    (((hasDerivAt_backwardD β μ 2 t x ht).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC))
  convert h1.add h2 using 1
  · funext y
    rfl
  · dsimp [backwardZxx, backwardZxxJet, backwardC] at *
    field_simp
    ring

theorem hasDerivAt_backwardQ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardQ β μ m (t, y))
      (backwardQxJet m (backwardC β μ (t, x)) (backwardD β μ 3 (t, x))
        (backwardD β μ 4 (t, x)) (backwardD β μ 5 (t, x))) x := by
  exact (hasDerivAt_backwardZx β hβ μ t x ht).sub
    ((hasDerivAt_backwardD β μ 2 t x ht).const_mul m)

theorem backwardQ_eq_derivZ_sub_mC (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardQ β μ m (t, x) = deriv (fun y => backwardZ β μ (t, y)) x - m * backwardC β μ (t, x) := by
  rw [(hasDerivAt_backwardZ β hβ μ t x ht).deriv]
  rfl

theorem backwardH_eq_z_sq_mC_sub_twoQ (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ) (p : ℝ × ℝ) :
    backwardH β μ m p = backwardZ β μ p ^ 2 + m * backwardC β μ p - 2 * backwardQ β μ m p := rfl

theorem hasDerivAt_backwardH (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardH β μ m (t, y)) (backwardHx β μ m (t, x)) x := by
  have hh := (((hasDerivAt_backwardZ β hβ μ t x ht).pow 2).add
    ((hasDerivAt_backwardD β μ 2 t x ht).const_mul m)).sub
    ((hasDerivAt_backwardQ β hβ μ m t x ht).const_mul 2)
  convert hh using 1
  · funext y
    rfl
  · dsimp [backwardHx, backwardHxJet, backwardZ, backwardZx]
    ring

theorem backwardHx_eq_derivH (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardHx β μ m (t, x) = deriv (fun y => backwardH β μ m (t, y)) x :=
  (hasDerivAt_backwardH β hβ μ m t x ht).deriv.symm

theorem backwardD_three_eq_neg_two_C_z (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardD β μ 3 (t, x) = -2 * backwardC β μ (t, x) * backwardZ β μ (t, x) :=
  Cx_eq_neg_two_C_z _ _ (backwardC_pos β hβ μ t x ht).ne'

end FRSB
