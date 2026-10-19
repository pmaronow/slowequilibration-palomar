module
public import Paper.ParisiTimeRegularity

@[expose] public section

/-! Literal logarithmic-curvature jets and the atom updates from Section 3.
The scalar jet formulas are identified with the actual selected Parisi
potential's spatial derivatives below. -/

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardZJet (C D : ℝ) : ℝ := -D / (2 * C)
def backwardZxJet (C D E : ℝ) : ℝ := -E / (2 * C) + D ^ 2 / (2 * C ^ 2)
def backwardZxxJet (C D E F : ℝ) : ℝ :=
  -F / (2 * C) + 3 * D * E / (2 * C ^ 2) - D ^ 3 / C ^ 3
def backwardQJet (m C D E : ℝ) : ℝ := backwardZxJet C D E - m * C
def backwardQxJet (m C D E F : ℝ) : ℝ := backwardZxxJet C D E F - m * D
def backwardHJet (m C D E : ℝ) : ℝ :=
  backwardZJet C D ^ 2 + m * C - 2 * backwardQJet m C D E
def backwardHxJet (m C D E F : ℝ) : ℝ :=
  2 * backwardZJet C D * backwardZxJet C D E + m * D - 2 * backwardQxJet m C D E F

def backwardD (β : ℝ) (μ : Paper.ParisiMeasure) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  Paper.parisiSpatialField β μ n p
def backwardB (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ := backwardD β μ 1 p
def backwardC (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ := backwardD β μ 2 p
def backwardZ (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ :=
  backwardZJet (backwardC β μ p) (backwardD β μ 3 p)
def backwardZx (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ :=
  backwardZxJet (backwardC β μ p) (backwardD β μ 3 p) (backwardD β μ 4 p)
def backwardZxx (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ :=
  backwardZxxJet (backwardC β μ p) (backwardD β μ 3 p) (backwardD β μ 4 p) (backwardD β μ 5 p)
def backwardQ (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardQJet m (backwardC β μ p) (backwardD β μ 3 p) (backwardD β μ 4 p)
def backwardH (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardHJet m (backwardC β μ p) (backwardD β μ 3 p) (backwardD β μ 4 p)
def backwardHx (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardHxJet m (backwardC β μ p) (backwardD β μ 3 p) (backwardD β μ 4 p) (backwardD β μ 5 p)

theorem backwardB_eq_gradient (β : ℝ) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardB β μ (t, x) = Paper.parisiGradient β μ (t, x) := by
  rw [backwardB, backwardD, Paper.parisiSpatialField_eq_iteratedDeriv β μ 1 t x ht,
    Paper.iteratedDeriv_parisiPotential_eq_gradient β μ 0 t x ht, iteratedDeriv_zero]

theorem backwardC_eq_hessian (β : ℝ) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardC β μ (t, x) = Paper.parisiHessian β μ (t, x) := by
  rw [backwardC, backwardD, Paper.parisiSpatialField_eq_iteratedDeriv β μ 2 t x ht]
  simpa only [iteratedDeriv_one, Paper.parisiHessian] using
    Paper.iteratedDeriv_parisiPotential_eq_gradient β μ 1 t x ht

theorem backwardC_pos (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < backwardC β μ (t, x) := by
  rw [backwardC_eq_hessian β μ t x ht]
  exact Paper.parisiHessian_pos β hβ μ t x ht

theorem backwardC_le_one (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : backwardC β μ (t, x) ≤ 1 := by
  rw [backwardC_eq_hessian β μ t x ht]
  exact Paper.parisiHessian_le_one β hβ μ (t, x)

lemma Cx_eq_neg_two_C_z (C D : ℝ) (hC : C ≠ 0) : D = -2 * C * backwardZJet C D := by
  unfold backwardZJet
  field_simp

lemma backwardHx_eq_zQ_Qx (m C D E F : ℝ) (hC : C ≠ 0) :
    backwardHxJet m C D E F =
      2 * backwardZJet C D * backwardQJet m C D E - 2 * backwardQxJet m C D E F := by
  unfold backwardHxJet backwardQJet backwardZJet
  field_simp
  ring

/-- The three weighted atom updates in the paper. -/
theorem backward_atom_updates (m δ C D E F : ℝ) (hC : C ≠ 0) :
    C * backwardQJet (m - δ) C D E = C * backwardQJet m C D E + δ * C ^ 2 ∧
    backwardZJet C D = backwardZJet C D ∧
    C * backwardHxJet (m - δ) C D E F =
      C * backwardHxJet m C D E F + 6 * δ * C ^ 2 * backwardZJet C D := by
  constructor
  · unfold backwardQJet
    ring
  constructor
  · rfl
  · unfold backwardHxJet backwardQxJet backwardZJet
    field_simp
    ring

/-- All five barrier increments across a backwards atom are literal algebra. -/
theorem backward_barrier_atom_updates (m δ B C D E F : ℝ) (hC : C ≠ 0) :
    (1 - (m - δ)) * C - C * backwardQJet (m - δ) C D E =
      (1 - m) * C - C * backwardQJet m C D E + δ * C * (1 - C) ∧
    (m - δ) * B + 1 - (m - δ) - backwardZJet C D =
      m * B + 1 - m - backwardZJet C D + δ * (1 - B) ∧
    6 * (1 - (m - δ)) * C - C * backwardHxJet (m - δ) C D E F =
      6 * (1 - m) * C - C * backwardHxJet m C D E F +
        6 * δ * C * (1 - C * backwardZJet C D) := by
  rw [(backward_atom_updates m δ C D E F hC).1,
    (backward_atom_updates m δ C D E F hC).2.2]
  constructor
  · ring
  constructor <;> ring

theorem backward_atom_increments_nonneg (δ B C z : ℝ)
    (hδ : 0 ≤ δ) (hB : B ≤ 1) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ δ * C ^ 2 ∧ 0 ≤ δ * C * (1 - C) ∧ 0 ≤ δ * (1 - B) ∧
      0 ≤ 6 * δ * C ^ 2 * z ∧ 0 ≤ 6 * δ * C * (1 - C * z) := by
  have hcz : C * z ≤ 1 := mul_le_one₀ hC1 hz0 hz1
  repeat' constructor
  · positivity
  · exact mul_nonneg (mul_nonneg hδ hC0) (sub_nonneg.mpr hC1)
  · exact mul_nonneg hδ (sub_nonneg.mpr hB)
  · positivity
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr hcz)

/-- Uniform terminal norm estimate used by the relative derivative barrier. -/
theorem terminal_derivative_polynomial_le (B : ℝ) (hB : B ^ 2 ≤ 1) :
    576 * B ^ 6 - 732 * B ^ 4 + 236 * B ^ 2 + 5 ≤ 85 := by
  have hp : 0 < 576 * B ^ 4 - 156 * B ^ 2 + 80 := by
    nlinarith [sq_nonneg (24 * B ^ 2 - (13 / 4 : ℝ))]
  have hh := mul_nonneg (sub_nonneg.mpr hB) hp.le
  nlinarith

end FRSB
