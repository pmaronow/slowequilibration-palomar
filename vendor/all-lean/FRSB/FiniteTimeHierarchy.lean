module
public import FRSB.OptimalDiffusion
public import FRSB.MixedPartial
public import Paper.ParisiPDEFormula
public import Paper.ParisiFiniteCells

@[expose] public section

/-! All-order actual spatial/time hierarchy on finite Cole–Hopf cells. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace FRSB

 theorem contDiff_parisiSpatialJet_succ (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (s : ℝ) :
    ContDiff ℝ ∞ (fun x => parisiSpatialJet β μ (j+1) s x) := by
  simp_rw [parisiSpatialJet_succ_eq_gradient_derivative, iteratedDeriv_eq_iterate]
  exact (Paper.contDiff_parisiGradient_spatial β μ s).iterate_deriv j

/-- Differentiated time forcing, defined literally as a spatial derivative of
 the actual Parisi PDE right-hand side. -/
def cellTimeForcing (β : ℝ) (μ : ParisiMeasure) (m : ℝ) (j : ℕ) (s x : ℝ) : ℝ :=
  iteratedDeriv j (fun y => -(β ^ 2 / 2) *
    (parisiSpatialJet β μ 2 s y + m * (parisiSpatialJet β μ 1 s y)^2)) x

 theorem contDiff_cellTimeBase (β : ℝ) (μ : ParisiMeasure) (m s : ℝ) :
    ContDiff ℝ ∞ (fun y => -(β ^ 2 / 2) *
      (parisiSpatialJet β μ 2 s y + m * (parisiSpatialJet β μ 1 s y)^2)) :=
  contDiff_const.mul ((contDiff_parisiSpatialJet_succ β μ 1 s).add
    (contDiff_const.mul ((contDiff_parisiSpatialJet_succ β μ 0 s).pow 2)))

 theorem cellTimeForcing_eq (β : ℝ) (μ : ParisiMeasure) (m : ℝ) (j : ℕ) (s x : ℝ) :
    cellTimeForcing β μ m j s x = -(β ^ 2 / 2) *
      (parisiSpatialJet β μ (j+2) s x + m * ∑ k ∈ Finset.range (j+1),
        (j.choose k : ℝ) * parisiSpatialJet β μ (k+1) s x *
          parisiSpatialJet β μ (j-k+1) s x) := by
  unfold cellTimeForcing
  rw [iteratedDeriv_const_mul_field]
  have h2 := (contDiff_parisiSpatialJet_succ β μ 1 s).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)
  have h1 := (contDiff_parisiSpatialJet_succ β μ 0 s).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedDeriv_fun_add h2.contDiffAt (by fun_prop), iteratedDeriv_const_mul_field]
  have he2 : iteratedDeriv j (fun y => parisiSpatialJet β μ 2 s y) x =
      parisiSpatialJet β μ (j+2) s x := by
    simp_rw [show (2 : ℕ) = 1+1 by norm_num, parisiSpatialJet_succ_eq_gradient_derivative]
    simp only [iteratedDeriv_one]
    rw [← iteratedDeriv_succ']
  rw [he2]
  congr 2
  have hepow : (fun y => (parisiSpatialJet β μ 1 s y)^2) =
      (fun y => parisiSpatialJet β μ 1 s y) * (fun y => parisiSpatialJet β μ 1 s y) := by
    ext y
    simp [pow_two]
  rw [hepow, iteratedDeriv_mul h1.contDiffAt h1.contDiffAt]
  simp_rw [parisiSpatialJet_succ_eq_gradient_derivative, iteratedDeriv_zero]

 theorem continuous_cellTimeForcing (β : ℝ) (μ : ParisiMeasure) (m : ℝ) (j : ℕ) :
    Continuous (fun p : ℝ × ℝ => cellTimeForcing β μ m j p.1 p.2) := by
  simp_rw [cellTimeForcing_eq]
  apply Continuous.const_mul
  apply Continuous.add (continuous_parisiSpatialJet_succ β μ (j+1))
  apply Continuous.const_mul
  exact continuous_finsetSum _ fun k _ =>
    ((continuous_parisiSpatialJet_succ β μ k).const_mul _).mul
      (continuous_parisiSpatialJet_succ β μ (j-k))

 theorem bounded_cellTimeForcing (β : ℝ) (μ : ParisiMeasure) (m : ℝ) (j : ℕ) :
    ∃ B : ℝ, ∀ s x, ‖cellTimeForcing β μ m j s x‖ ≤ B := by
  let K : ℕ → ℝ := fun n => ‖Paper.bcfSpatialDerivative (Paper.parisiGradientBCF β μ) n‖
  refine ⟨‖-(β ^ 2 / 2)‖ * (K (j+1) + ‖m‖ *
    ∑ k ∈ Finset.range (j+1), ‖(j.choose k : ℝ)‖ * K k * K (j-k)), ?_⟩
  intro s x
  rw [cellTimeForcing_eq, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_parisiSpatialJet_succ_le β μ (j+1) s x)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, norm_mul]
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_parisiSpatialJet_succ_le β μ k s x) (norm_nonneg _))
    (norm_parisiSpatialJet_succ_le β μ (j-k) s x) (norm_nonneg _)
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

 theorem hasDerivAt_cellTimeForcing_spatial (β : ℝ) (μ : ParisiMeasure) (m : ℝ)
    (j : ℕ) (s x : ℝ) :
    HasDerivAt (cellTimeForcing β μ m j s) (cellTimeForcing β μ m (j+1) s x) x := by
  unfold cellTimeForcing
  have hd := (contDiff_cellTimeBase β μ m s).differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top j) x
  simpa only [iteratedDeriv_succ] using hd.hasDerivAt

/-- The hierarchy follows from the genuine base PDE and actual spatial jets.
The auxiliary base PDE premise will be discharged for every finite cell below. -/
theorem time_hierarchy_of_base_PDE (β : ℝ) (μ : ParisiMeasure) (m a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hPDE : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun s => parisiSpatialJet β μ 0 s x)
        (cellTimeForcing β μ m 0 t x) t) :
    ∀ j t, t ∈ Ioo a b → ∀ x,
      HasDerivAt (fun s => parisiSpatialJet β μ j s x)
        (cellTimeForcing β μ m j t x) t := by
  intro j
  induction j with
  | zero => exact hPDE
  | succ j ih =>
    intro t ht x
    obtain ⟨B,hB⟩ := bounded_cellTimeForcing β μ m (j+1)
    exact hasDerivAt_time_spatial_of_FTC
      (parisiSpatialJet β μ j) (parisiSpatialJet β μ (j+1))
      (cellTimeForcing β μ m j) (cellTimeForcing β μ m (j+1))
      (continuous_cellTimeForcing β μ m j) (continuous_cellTimeForcing β μ m (j+1))
      a b B ih
      (fun s hs y => hasDerivAt_parisiSpatialJet β μ j s y ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩)
      (fun s _ y => hasDerivAt_cellTimeForcing_spatial β μ m j s y)
      (fun s _ y => hB s y) ht

/-- Actual gradient and Hessian values on a finite physical cell. -/
theorem finiteCell_jet_one_two {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) {t : ℝ} (ht : t ∈ Icc (s.q p) (s.q (p+1)))
    (x : ℝ) :
    parisiSpatialJet β (Paper.parisiSchemeMeasure s) 1 t x =
      Paper.parisiSlabGradient s β (k+1-p) (s.m p) (s.q (p+1)) t x ∧
    parisiSpatialJet β (Paper.parisiSchemeMeasure s) 2 t x =
      Paper.parisiSlabHessian s β (k+1-p) (s.m p) (s.q (p+1)) t x := by
  have he (y : ℝ) : parisiSpatialJet β (Paper.parisiSchemeMeasure s) 1 t y =
      Paper.parisiSlabGradient s β (k+1-p) (s.m p) (s.q (p+1)) t y := by
    rw [parisiSpatialJet_one, Paper.parisiSchemeGradient_eq_actual s β hβ]
    exact Paper.parisiFiniteGradient_eq_slab s β hp hq ht y
  refine ⟨he x, ?_⟩
  have hd := Paper.hasDerivAt_parisiSlabGradient_spatial s β (k+1-p) (s.m p) (s.q (p+1)) t x
  have hefun := funext he
  exact (hasDerivAt_parisiSpatialJet_succ β (Paper.parisiSchemeMeasure s) 0 t x).unique
    (hefun ▸ hd)

/-- The full all-order time hierarchy for a genuine finite Parisi measure;
no differentiated-PDE premise is supplied by the caller. -/
theorem hasDerivAt_finiteCell_spatialJet_time {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (s.q p) (s.q (p+1))) (x : ℝ) :
    HasDerivAt (fun r => parisiSpatialJet β (Paper.parisiSchemeMeasure s) j r x)
      (cellTimeForcing β (Paper.parisiSchemeMeasure s) (s.m p) j t x) t := by
  apply time_hierarchy_of_base_PDE β (Paper.parisiSchemeMeasure s) (s.m p)
    (s.q p) (s.q (p+1)) (s.q_nonneg (by omega)) (s.q_le_one (by omega)) ?_ j t ht x
  intro r hr y
  have he : (fun r => parisiSpatialJet β (Paper.parisiSchemeMeasure s) 0 r y) =ᶠ[nhds r]
      (fun r => Paper.parisiSlabPotential s β (k+1-p) (s.m p) (s.q (p+1)) r y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with v hv
    simp only [parisiSpatialJet, ite_true]
    rw [Paper.parisiSchemePotential_eq_actual s β hβ v y
      ⟨(s.q_nonneg (by omega)).trans hv.1.le, hv.2.le.trans (s.q_le_one (by omega))⟩]
    exact Paper.parisiFinitePotential_eq_slab s β hp hq ⟨hv.1.le,hv.2.le⟩ y
  have hjet := finiteCell_jet_one_two s β hβ hp hq ⟨hr.1.le,hr.2.le⟩ y
  have hd := (Paper.hasDerivAt_parisiSlabPotential_time s β hβ (k+1-p)
    (s.m p) (s.q (p+1)) y hr.2).congr_of_eventuallyEq he
  simpa only [cellTimeForcing, iteratedDeriv_zero, hjet.1, hjet.2] using hd

end FRSB
