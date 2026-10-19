module
public import FRSB.ForwardHigherHeat
public import Paper.ParisiCurvature
public import Paper.ParisiSpatialSmooth

@[expose] public section

/-! Spatial symmetry of the actual finite and limiting Parisi solutions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace FRSB
open SpinGlass SpinGlass.Targets

lemma gaussianExpectation_reflect (f : ℝ → ℝ) (hf : Measurable f) :
    Paper.gaussianExpectation (fun z => f (-z)) = Paper.gaussianExpectation f := by
  unfold Paper.gaussianExpectation
  calc
    _ = ∫ z, f z ∂(gaussianReal 0 1).map (fun z => -z) :=
      (integral_map (by fun_prop) hf.aestronglyMeasurable).symm
    _ = _ := by rw [gaussianReal_map_neg]; simp

lemma gaussianScaledAverage_even (θ b : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (heven : ∀ y, f (-y) = f y) (x : ℝ) :
    gaussianScaledAverage θ b f (-x) = gaussianScaledAverage θ b f x := by
  unfold gaussianScaledAverage
  rw [← gaussianExpectation_reflect (fun z => f (θ * (-x) + b * z)) (hf.comp (by fun_prop))]
  congr 1
  ext z
  rw [show θ * (-x) + b * (-z) = -(θ * x + b * z) by ring, heven]

lemma parisiStep_even (m v : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (heven : ∀ y, f (-y) = f y) (x : ℝ) : parisiStep m v f (-x) = parisiStep m v f x := by
  have he := gaussianScaledAverage_even 1 (Real.sqrt v) f hf heven x
  have heexp := gaussianScaledAverage_even 1 (Real.sqrt v) (fun y => Real.exp (m * f y))
    (by fun_prop) (fun y => by rw [heven]) x
  simp only [gaussianScaledAverage, Paper.gaussianExpectation, one_mul] at he heexp
  unfold parisiStep
  split_ifs
  · exact he
  · rw [heexp]

lemma parisiF_even {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    parisiF s β j (-x) = parisiF s β j x := by
  induction j generalizing x with
  | zero => simp [parisiF]
  | succ j ih =>
    exact parisiStep_even _ _ _ (parisiF_measurable s β j) ih x

lemma parisiFinitePotentialAux_even {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (t x : ℝ) :
    Paper.parisiFinitePotentialAux s β j t (-x) = Paper.parisiFinitePotentialAux s β j t x := by
  induction j with
  | zero => exact parisiF_even s β 0 x
  | succ j ih =>
    unfold Paper.parisiFinitePotentialAux
    split_ifs
    · exact parisiStep_even _ _ _ (parisiF_measurable s β j) (parisiF_even s β j) x
    · exact ih

lemma parisiFinitePotential_even {k : ℕ} (s : RSBScheme k) (β t x : ℝ) :
    Paper.parisiFinitePotential s β (t, -x) = Paper.parisiFinitePotential s β (t, x) :=
  parisiFinitePotentialAux_even s β _ _ x

/-- The actual selected potential is even, not just its finite approximants. -/
theorem parisiPotential_even (β : ℝ) (μ : Paper.ParisiMeasure) (t x : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Paper.parisiPotential β μ (t, -x) = Paper.parisiPotential β μ (t, x) := by
  by_cases hβ : β = 0
  · subst β
    simp only [Paper.parisiPotential_zero, Real.cosh_neg]
  · have h1 := Paper.tendsto_actual_finiteParisiPotential β hβ μ t (-x) ht
    have h2 := Paper.tendsto_actual_finiteParisiPotential β hβ μ t x ht
    simp_rw [parisiFinitePotential_even] at h1
    exact tendsto_nhds_unique h1 h2

/-- All spatial derivatives inherit their exact even/odd parity. -/
theorem parisiPotential_iteratedDeriv_parity (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y => Paper.parisiPotential β μ (t, y)) (-x) =
      (-1 : ℝ) ^ j * iteratedDeriv j (fun y => Paper.parisiPotential β μ (t, y)) x := by
  let f := fun y => Paper.parisiPotential β μ (t, y)
  have he : (fun y => f (-y)) = f := funext (parisiPotential_even β μ t · ht)
  have hh := iteratedDeriv_comp_neg j f x
  rw [he] at hh
  simp only [smul_eq_mul] at hh
  have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * iteratedDeriv j f (-x) := by rw [hsq, one_mul]
    _ = (-1 : ℝ) ^ j * iteratedDeriv j f x := by rw [mul_assoc, ← hh]

/-- The actual gradient is odd and vanishes at the origin. -/
theorem parisiGradient_odd (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Paper.parisiGradient β μ (t, -x) = -Paper.parisiGradient β μ (t, x) := by
  have hh := parisiPotential_iteratedDeriv_parity β μ t ht 1 x
  simpa only [iteratedDeriv_one, (Paper.hasDerivAt_parisiPotential_spatial β hβ μ t (-x) ht).deriv,
    (Paper.hasDerivAt_parisiPotential_spatial β hβ μ t x ht).deriv, pow_one, neg_one_mul] using hh

@[simp] theorem parisiGradient_at_zero (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Paper.parisiGradient β μ (t, 0) = 0 := by
  have hh := parisiGradient_odd β hβ μ t 0 ht
  rw [neg_zero] at hh
  linarith

end FRSB
