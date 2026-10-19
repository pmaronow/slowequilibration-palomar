module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import SlowEquilibration.FrameParseval
public import SlowEquilibration.BumpShell
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Continuum bump averaging

The parameter measure in manuscript `lem:sp-bumps` is normalized Lebesgue
measure on the ball of radius `1+ρ`. These results work for an actual Haar
measure on any finite-dimensional real normed space, hence apply to Lebesgue
measure on `EuclideanSpace ℝ (Fin N)`.
-/

namespace SlowEquilibration

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

section Haar

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [borel : BorelSpace E]

/-- The actual continuum parameter measure used for translated bumps.
Taking `ν = volume` gives the manuscript's normalized restricted Lebesgue
measure. -/
noncomputable def bumpIndexMeasure (ν : Measure E) (ρ : ℝ) : Measure E :=
  (ν (closedBall (0 : E) ρ))⁻¹ • ν.restrict (closedBall (0 : E) (1 + ρ))

omit borel

/-- The normalized continuum parameter measure is finite. -/
theorem bumpIndexMeasure_isFinite (ν : Measure E) [IsAddHaarMeasure ν]
    (ρ : ℝ) (hρ : 0 < ρ) : IsFiniteMeasure (bumpIndexMeasure ν ρ) := by
  let : IsFiniteMeasure (ν.restrict (closedBall (0 : E) (1 + ρ))) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  exact (ν.restrict (closedBall (0 : E) (1 + ρ))).smul_finite
    (ENNReal.inv_ne_top.mpr (measure_closedBall_pos ν 0 hρ).ne')

include borel

/-- Every translated ball of radius `a*ρ`, with `0≤a≤1` and center in the
unit ball, has normalized parameter mass `a^dim`. This is a continuum
volume calculation, not a finite trial surrogate. -/
theorem bumpIndexMeasure_closedBall (ν : Measure E) [IsAddHaarMeasure ν]
    (ρ a : ℝ) (b : E) (hρ : 0 < ρ) (ha : 0 ≤ a) (haone : a ≤ 1)
    (hb : ‖b‖ ≤ 1) :
    bumpIndexMeasure ν ρ (closedBall b (a * ρ)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E) := by
  have hsubset : closedBall b (a * ρ) ⊆ closedBall (0 : E) (1 + ρ) := by
    apply closedBall_subset_closedBall'
    rw [dist_zero_right]
    nlinarith
  have hDzero : ν (closedBall (0 : E) ρ) ≠ 0 :=
    (measure_closedBall_pos ν 0 hρ).ne'
  have hDtop : ν (closedBall (0 : E) ρ) ≠ ∞ := measure_closedBall_lt_top.ne
  rw [bumpIndexMeasure, Measure.smul_apply, Measure.restrict_apply measurableSet_closedBall,
    Set.inter_eq_left.mpr hsubset, addHaar_closedBall_mul ν b ha hρ.le]
  change (ν (closedBall (0 : E) ρ))⁻¹ *
      (ENNReal.ofReal (a ^ Module.finrank ℝ E) * ν (closedBall (0 : E) ρ)) = _
  calc
    _ = ((ν (closedBall (0 : E) ρ))⁻¹ * ν (closedBall (0 : E) ρ)) *
        ENNReal.ofReal (a ^ Module.finrank ℝ E) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hDzero hDtop, one_mul]

/-- In particular, a bump's support ball has parameter mass one. -/
theorem bumpIndexMeasure_supportBall (ν : Measure E) [IsAddHaarMeasure ν]
    (ρ : ℝ) (b : E) (hρ : 0 < ρ) (hb : ‖b‖ ≤ 1) :
    bumpIndexMeasure ν ρ (closedBall b ρ) = 1 := by
  simpa using bumpIndexMeasure_closedBall ν ρ 1 b hρ zero_le_one le_rfl hb

end Haar

/-- The manuscript's actual radial scalar cutoff, before composition with
the observable `B`. -/
noncomputable def translatedBump (α : ℝ → ℝ) (N ρ : ℝ) (b z : E) : ℝ :=
  α (N * (1 - ‖b - z‖ ^ 2 / ρ ^ 2))

/-- A positive bump lies strictly inside its support ball. -/
theorem translatedBump_support (α : ℝ → ℝ) (N ρ : ℝ) (b z : E)
    (hN : 0 < N) (hρ : 0 < ρ) (hαzero : ∀ t ≤ 0, α t = 0)
    (hpositive : 0 < translatedBump α N ρ b z) : ‖b - z‖ < ρ := by
  have harg : 0 < N * (1 - ‖b - z‖ ^ 2 / ρ ^ 2) := by
    by_contra h
    have hz := hαzero _ (le_of_not_gt h)
    simp [translatedBump, hz] at hpositive
  have hfactor : 0 < 1 - ‖b - z‖ ^ 2 / ρ ^ 2 :=
    (mul_pos_iff_of_pos_left hN).mp harg
  have hsq : ‖b - z‖ ^ 2 < ρ ^ 2 :=
    (div_lt_one (sq_pos_of_pos hρ)).mp (by linarith)
  nlinarith [norm_nonneg (b - z)]

/-- A bump equals one on its inner ball. The inequality on the radius is
stated squared so that no approximation of its square root is required. -/
theorem translatedBump_one (α : ℝ → ℝ) (N ρ : ℝ) (b z : E)
    (hN : 0 < N) (hρ : 0 < ρ) (hαone : ∀ t, 1 ≤ t → α t = 1)
    (hinner : ‖b - z‖ ^ 2 ≤ ρ ^ 2 * (1 - 1 / N)) :
    translatedBump α N ρ b z = 1 := by
  apply hαone
  have hdiv : ‖b - z‖ ^ 2 / ρ ^ 2 ≤ 1 - 1 / N :=
    (div_le_iff₀ (sq_pos_of_pos hρ)).2 (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hdiv hN.le
  have hcancel : N * (1 - 1 / N) = N - 1 := by
    field_simp [ne_of_gt hN]
  nlinarith

/-- The actual translated scalar cutoff is continuous in its center. -/
theorem translatedBump_continuous (α : ℝ → ℝ) (N ρ : ℝ) (b : E)
    (hα : Continuous α) : Continuous (translatedBump α N ρ b) := by
  unfold translatedBump
  fun_prop

section Haar

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The continuum column bound for the explicit radial cutoff and the
normalized restricted Haar parameter measure. -/
theorem averaged_translatedBump_column (ν : Measure E) [IsAddHaarMeasure ν]
    (α : ℝ → ℝ) (N ρ : ℝ) (b : E) (hN : 0 < N) (hρ : 0 < ρ)
    (hb : ‖b‖ ≤ 1) (hα : Continuous α)
    (hαnonneg : ∀ t, 0 ≤ α t) (hαbound : ∀ t, α t ≤ 1)
    (hαzero : ∀ t ≤ 0, α t = 0) :
    Integrable (translatedBump α N ρ b) (bumpIndexMeasure ν ρ) ∧
      (∫ z, translatedBump α N ρ b z ∂bumpIndexMeasure ν ρ) ≤ 1 := by
  let μ := bumpIndexMeasure ν ρ
  let : IsFiniteMeasure μ := bumpIndexMeasure_isFinite ν ρ hρ
  have hnonneg : ∀ z, 0 ≤ translatedBump α N ρ b z := fun _ => hαnonneg _
  have hbound : ∀ z, translatedBump α N ρ b z ≤ 1 := fun _ => hαbound _
  have hmeas : AEStronglyMeasurable (translatedBump α N ρ b) μ :=
    (translatedBump_continuous α N ρ b hα).aestronglyMeasurable
  have hInt : Integrable (translatedBump α N ρ b) μ := by
    apply (integrable_const (1 : ℝ)).mono' hmeas
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (hnonneg z)]
      exact hbound z)
  refine ⟨hInt, ?_⟩
  have hpoint : ∀ z, translatedBump α N ρ b z ≤ (closedBall b ρ).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ closedBall b ρ
    · simpa [hz] using hbound z
    · have hbump : translatedBump α N ρ b z ≤ 0 := by
        by_contra h
        have hs := translatedBump_support α N ρ b z hN hρ hαzero (lt_of_not_ge h)
        exact hz (by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs.le)
      simpa [hz] using hbump
  have hballInt : Integrable ((closedBall b ρ).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
  calc
    _ ≤ ∫ z, (closedBall b ρ).indicator (fun _ => (1 : ℝ)) z ∂μ :=
      integral_mono_ae hInt hballInt (Filter.Eventually.of_forall hpoint)
    _ = μ.real (closedBall b ρ) := by
      rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall]
      simp
    _ = 1 := by simp [μ, measureReal_def, bumpIndexMeasure_supportBall ν ρ b hρ hb]

/-- The actual continuum squared bump mass is between the volume fraction
of its inner ball and one. The inner radius ratio is arbitrary; the manuscript
takes `a = sqrt (1-1/N)` and proves the uniform lower fraction `1/2`. -/
theorem averaged_translatedBump_square_mass (ν : Measure E) [IsAddHaarMeasure ν]
    (α : ℝ → ℝ) (N ρ a : ℝ) (b : E) (hN : 0 < N) (hρ : 0 < ρ)
    (ha : 0 ≤ a) (haone : a ≤ 1) (haInner : a ^ 2 ≤ 1 - 1 / N)
    (hb : ‖b‖ ≤ 1) (hα : Continuous α)
    (hαnonneg : ∀ t, 0 ≤ α t) (hαbound : ∀ t, α t ≤ 1)
    (hαzero : ∀ t ≤ 0, α t = 0) (hαone : ∀ t, 1 ≤ t → α t = 1) :
    Integrable (fun z => (translatedBump α N ρ b z) ^ 2) (bumpIndexMeasure ν ρ) ∧
      a ^ Module.finrank ℝ E ≤
        (∫ z, (translatedBump α N ρ b z) ^ 2 ∂bumpIndexMeasure ν ρ) ∧
      (∫ z, (translatedBump α N ρ b z) ^ 2 ∂bumpIndexMeasure ν ρ) ≤ 1 := by
  let μ := bumpIndexMeasure ν ρ
  let : IsFiniteMeasure μ := bumpIndexMeasure_isFinite ν ρ hρ
  have hcolumn := averaged_translatedBump_column ν α N ρ b hN hρ hb hα
    hαnonneg hαbound hαzero
  have hnonneg : ∀ z, 0 ≤ translatedBump α N ρ b z := fun _ => hαnonneg _
  have hbound : ∀ z, translatedBump α N ρ b z ≤ 1 := fun _ => hαbound _
  have hsquarele : ∀ z, (translatedBump α N ρ b z) ^ 2 ≤ translatedBump α N ρ b z :=
    fun z => by nlinarith [hnonneg z, hbound z]
  have hInt : Integrable (fun z => (translatedBump α N ρ b z) ^ 2) μ :=
    hcolumn.1.mono_nonneg ((translatedBump_continuous α N ρ b hα).aestronglyMeasurable.pow 2)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall hsquarele)
  refine ⟨hInt, ?_, ?_⟩
  · have hpoint : ∀ z, (closedBall b (a * ρ)).indicator (fun _ => (1 : ℝ)) z ≤
        (translatedBump α N ρ b z) ^ 2 := by
      intro z
      by_cases hz : z ∈ closedBall b (a * ρ)
      · have hnorm : ‖b - z‖ ≤ a * ρ := by
          simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
        have hnormsq : ‖b - z‖ ^ 2 ≤ (a * ρ) ^ 2 := by
          nlinarith [norm_nonneg (b - z), mul_nonneg ha hρ.le]
        have hinner : ‖b - z‖ ^ 2 ≤ ρ ^ 2 * (1 - 1 / N) := by
          calc
            _ ≤ (a * ρ) ^ 2 := hnormsq
            _ = ρ ^ 2 * a ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left haInner (sq_nonneg ρ)
        simp [hz, translatedBump_one α N ρ b z hN hρ hαone hinner]
      · simpa [hz] using sq_nonneg (translatedBump α N ρ b z)
    have hballInt : Integrable ((closedBall b (a * ρ)).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
    calc
      _ = μ.real (closedBall b (a * ρ)) := by
        simp [μ, measureReal_def, bumpIndexMeasure_closedBall ν ρ a b hρ ha haone hb,
          ENNReal.toReal_ofReal (pow_nonneg ha _)]
      _ = ∫ z, (closedBall b (a * ρ)).indicator (fun _ => (1 : ℝ)) z ∂μ := by
        rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall]
        simp
      _ ≤ _ := integral_mono_ae hballInt hInt (Filter.Eventually.of_forall hpoint)
  · exact (integral_mono_ae hInt hcolumn.1 (Filter.Eventually.of_forall hsquarele)).trans hcolumn.2

end Haar

section StateSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {X : Type*} [MeasurableSpace X]

/-- Joint measurability of the explicit translated-bump family. -/
theorem translatedBump_family_measurable (α : ℝ → ℝ) (N ρ : ℝ) (B : X → E)
    (hα : Continuous α) (hB : Measurable B) :
    Measurable (fun z : E × X => translatedBump α N ρ (B z.2) z.1) := by
  have hsq : Measurable (fun z : E × X => ‖B z.2 - z.1‖ ^ 2) :=
    (((hB.comp measurable_snd).sub measurable_fst).norm).pow_const 2
  exact hα.measurable.comp (measurable_const.mul (measurable_const.sub (hsq.div measurable_const)))

/-- The total trace of the actual `L²` continuum bump family is between
the inner-ball volume fraction and one. The `L²` norm is converted to the
actual state integral from its representative, and Fubini proves the trace
bounds from the previously derived column bounds. -/
theorem translatedBump_family_trace_bounds (ν : Measure E) [IsAddHaarMeasure ν]
    (π : Measure X) [IsProbabilityMeasure π]
    (α : ℝ → ℝ) (N ρ a : ℝ) (B : X → E) (F : E → Lp ℝ 2 π)
    (hN : 0 < N) (hρ : 0 < ρ) (ha : 0 ≤ a) (haone : a ≤ 1)
    (haInner : a ^ 2 ≤ 1 - 1 / N) (hB : Measurable B) (hBnorm : ∀ x, ‖B x‖ ≤ 1)
    (hα : Continuous α) (hαnonneg : ∀ t, 0 ≤ α t) (hαbound : ∀ t, α t ≤ 1)
    (hαzero : ∀ t ≤ 0, α t = 0) (hαone : ∀ t, 1 ≤ t → α t = 1)
    (hFrep : ∀ z, (fun x => translatedBump α N ρ (B x) z) =ᵐ[π] F z) :
    Integrable (fun z => ‖F z‖ ^ 2) (bumpIndexMeasure ν ρ) ∧
      a ^ Module.finrank ℝ E ≤ (∫ z, ‖F z‖ ^ 2 ∂bumpIndexMeasure ν ρ) ∧
      (∫ z, ‖F z‖ ^ 2 ∂bumpIndexMeasure ν ρ) ≤ 1 := by
  let μ := bumpIndexMeasure ν ρ
  let : IsFiniteMeasure μ := bumpIndexMeasure_isFinite ν ρ hρ
  let g : E × X → ℝ := fun z => (translatedBump α N ρ (B z.2) z.1) ^ 2
  have hgmeas : Measurable g := (translatedBump_family_measurable α N ρ B hα hB).pow_const 2
  have hgrange : ∀ z, 0 ≤ g z ∧ g z ≤ 1 := by
    intro z
    have h0 := hαnonneg (N * (1 - ‖B z.2 - z.1‖ ^ 2 / ρ ^ 2))
    have h1 := hαbound (N * (1 - ‖B z.2 - z.1‖ ^ 2 / ρ ^ 2))
    dsimp [g, translatedBump]
    constructor
    · exact sq_nonneg _
    · nlinarith
  have hgInt : Integrable g (μ.prod π) := by
    apply (integrable_const (1 : ℝ)).mono' hgmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (hgrange z).1]
      exact (hgrange z).2)
  have hnormeq : (fun z => ‖F z‖ ^ 2) = (fun z => ∫ x, g (z, x) ∂π) := by
    funext z
    exact (L2_representative_integrable_sq_and_norm π (F z)
      (fun x => translatedBump α N ρ (B x) z) (hFrep z)).2
  have hmassInt : Integrable (fun z => ‖F z‖ ^ 2) μ := hnormeq ▸ hgInt.integral_prod_left
  have hswap : (∫ z, ‖F z‖ ^ 2 ∂μ) = ∫ x, ∫ z, (translatedBump α N ρ (B x) z) ^ 2 ∂μ ∂π := by
    rw [hnormeq]
    exact integral_integral_swap hgInt
  have hcolumns : ∀ x,
      a ^ Module.finrank ℝ E ≤ (∫ z, (translatedBump α N ρ (B x) z) ^ 2 ∂μ) ∧
      (∫ z, (translatedBump α N ρ (B x) z) ^ 2 ∂μ) ≤ 1 := by
    intro x
    exact (averaged_translatedBump_square_mass ν α N ρ a (B x) hN hρ ha haone haInner
      (hBnorm x) hα hαnonneg hαbound hαzero hαone).2
  refine ⟨hmassInt, ?_, ?_⟩
  · rw [hswap]
    calc
      _ = ∫ _x, (a ^ Module.finrank ℝ E) ∂π := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hgInt.integral_prod_right
        (Filter.Eventually.of_forall (fun x => (hcolumns x).1))
  · rw [hswap]
    calc
      _ ≤ ∫ _x, (1 : ℝ) ∂π := integral_mono_ae hgInt.integral_prod_right (integrable_const _)
        (Filter.Eventually.of_forall (fun x => (hcolumns x).2))
      _ = 1 := by simp

/-- The exact trace bound `1/2 ≤ T ≤ 1` in `eq:sp-bump-mass`, with the
actual dimension, actual normalized Haar parameter measure, and actual `L²`
trial family. This holds in every finite dimension at least two. -/
theorem translatedBump_family_half_trace (ν : Measure E) [IsAddHaarMeasure ν]
    (π : Measure X) [IsProbabilityMeasure π]
    (α : ℝ → ℝ) (ρ : ℝ) (B : X → E) (F : E → Lp ℝ 2 π)
    (hdim : 2 ≤ Module.finrank ℝ E) (hρ : 0 < ρ)
    (hB : Measurable B) (hBnorm : ∀ x, ‖B x‖ ≤ 1)
    (hα : Continuous α) (hαnonneg : ∀ t, 0 ≤ α t) (hαbound : ∀ t, α t ≤ 1)
    (hαzero : ∀ t ≤ 0, α t = 0) (hαone : ∀ t, 1 ≤ t → α t = 1)
    (hFrep : ∀ z, (fun x => translatedBump α (Module.finrank ℝ E) ρ (B x) z) =ᵐ[π] F z) :
    Integrable (fun z => ‖F z‖ ^ 2) (bumpIndexMeasure ν ρ) ∧
      (1 / 2 : ℝ) ≤ (∫ z, ‖F z‖ ^ 2 ∂bumpIndexMeasure ν ρ) ∧
      (∫ z, ‖F z‖ ^ 2 ∂bumpIndexMeasure ν ρ) ≤ 1 := by
  have hdimReal : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
  have hN : (0 : ℝ) < Module.finrank ℝ E := by linarith
  have hbase : 0 ≤ 1 - 1 / (Module.finrank ℝ E : ℝ) := by
    have hdiv : 1 / (Module.finrank ℝ E : ℝ) ≤ 1 := (div_le_one₀ hN).2 (by linarith)
    linarith
  let a := Real.sqrt (1 - 1 / (Module.finrank ℝ E : ℝ))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have haInner : a ^ 2 = 1 - 1 / (Module.finrank ℝ E : ℝ) := Real.sq_sqrt hbase
  have haone : a ≤ 1 := by
    have hdiv : 0 ≤ 1 / (Module.finrank ℝ E : ℝ) := by positivity
    nlinarith
  have ht := translatedBump_family_trace_bounds ν π α (Module.finrank ℝ E) ρ a B F
    hN hρ ha haone haInner.le hB hBnorm hα hαnonneg hαbound hαzero hαone hFrep
  exact ⟨ht.1, (bump_shell_sqrt_pow_lower_bound (Module.finrank ℝ E) hdim).trans ht.2.1, ht.2.2⟩

end StateSpace

end SlowEquilibration
