module
public import Paper.ParisiState

@[expose] public section

/-! Integral Picard stability under a perturbation controlled in L¹ in time.
This permits moving discontinuities of a finite step coefficient. -/
noncomputable section
open Function MeasureTheory Metric Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
open Paper Paper.IntegralPicard

def integratedSensitivity (K : ℝ≥0) (T : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (K : ℝ)*T*integratedSensitivity K T n+1

theorem integratedSensitivity_nonneg {K : ℝ≥0} {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ integratedSensitivity K T n := by
  induction n with
  | zero => rfl
  | succ n hn => exact add_nonneg (mul_nonneg (mul_nonneg K.2 hT) hn) zero_le_one

theorem next_drift_integrated_dist_le {T h : ℝ} (hT : 0 ≤ T) {L K : ℝ≥0}
    {f g : ℝ → ℝ → ℝ} (hf : IsBoundedMeasurableDrift f L K)
    (hg : IsBoundedMeasurableDrift g L K) (e : ℝ → ℝ)
    (he : IntervalIntegrable e volume 0 T) (hne : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ e t)
    (hfg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, dist (f t x) (g t x) ≤ e t)
    (α : Curve hT h L) :
    dist (next hT hf α) (next hT hg α) ≤ ∫ t in 0..T, e t := by
  have hEn : 0 ≤ ∫ t in 0..T, e t := intervalIntegral.integral_nonneg hT
    (fun t ht => hne t ht)
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    rw [ODE.FunSpace.toContinuousMap_apply_eq_apply, ODE.FunSpace.toContinuousMap_apply_eq_apply,
      dist_eq_norm, next_apply, next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrable_comp hT hf α t) (integrable_comp hT hg α t)]
    have het : IntervalIntegrable e volume 0 (t : ℝ) :=
      he.mono_set (uIcc_subset_uIcc (by simp) (by simpa [uIcc_of_le hT] using t.property))
    calc
      _ ≤ ∫ s in 0..(t : ℝ), ‖f s (α.compProj s)-g s (α.compProj s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm t.property.1
      _ ≤ ∫ s in 0..(t : ℝ), e s := by
        apply intervalIntegral.integral_mono_on t.property.1
          ((integrable_comp hT hf α t).sub (integrable_comp hT hg α t)).norm het
        intro s hs
        rw [← dist_eq_norm]
        exact hfg s ⟨hs.1, hs.2.trans t.property.2⟩ _
      _ ≤ ∫ s in 0..T, e s := intervalIntegral.integral_mono_interval le_rfl
        t.property.1 t.property.2 (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hne s ⟨hs.1.le, hs.2⟩) he
  · exact hEn

theorem iterate_next_dist_le_of_step_bound {T h : ℝ} (hT : 0 ≤ T) {L K : ℝ≥0}
    {f g : ℝ → ℝ → ℝ} (hf : IsBoundedMeasurableDrift f L K)
    (hg : IsBoundedMeasurableDrift g L K) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ α : Curve hT h L, dist (next hT hf α) (next hT hg α) ≤ E)
    (α : Curve hT h L) (n : ℕ) :
    dist ((next hT hf)^[n] α) ((next hT hg)^[n] α) ≤ integratedSensitivity K T n*E := by
  induction n with
  | zero => simp [integratedSensitivity]
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply']
    calc
      _ ≤ dist (next hT hf ((next hT hf)^[n] α)) (next hT hf ((next hT hg)^[n] α)) +
          dist (next hT hf ((next hT hg)^[n] α)) (next hT hg ((next hT hg)^[n] α)) := dist_triangle _ _ _
      _ ≤ ((K : ℝ)*T)*(integratedSensitivity K T n*E)+E :=
        add_le_add ((next_dist_le hT hf _ _).trans
          (mul_le_mul_of_nonneg_left hn (mul_nonneg K.2 hT))) (hb _)
      _ = integratedSensitivity K T (n+1)*E := by simp only [integratedSensitivity]; ring

theorem solution_dist_le_of_integrated_drift_bound {T h : ℝ} (hT : 0 ≤ T) {L K : ℝ≥0}
    {f g : ℝ → ℝ → ℝ} (hf : IsBoundedMeasurableDrift f L K)
    (hg : IsBoundedMeasurableDrift g L K) (e : ℝ → ℝ)
    (he : IntervalIntegrable e volume 0 T) (hne : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ e t)
    (hfg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, dist (f t x) (g t x) ≤ e t)
    (n : ℕ) (hn : ((K : ℝ)*T)^n/n.factorial < 1) :
    dist (solution (h := h) hT hf) (solution (h := h) hT hg) ≤
      integratedSensitivity K T n/(1-((K : ℝ)*T)^n/n.factorial)*(∫ t in 0..T, e t) := by
  let E := ∫ t in 0..T, e t
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg hT (fun t ht => hne t ht)
  have hb := next_drift_integrated_dist_le (h := h) hT hf hg e he hne hfg
  let α := solution (h := h) hT hf
  let γ := solution (h := h) hT hg
  have ha : (next hT hf)^[n] α = α := (solution_fixed hT hf).iterate n
  have hg' : (next hT hg)^[n] γ = γ := (solution_fixed hT hg).iterate n
  have hd : dist α γ ≤ ((K : ℝ)*T)^n/n.factorial*dist α γ+integratedSensitivity K T n*E := by
    nth_rw 1 [← ha, ← hg']
    exact (dist_triangle _ ((next hT hf)^[n] γ) _).trans
      (add_le_add (dist_iterate_le hT hf α γ n)
        (iterate_next_dist_le_of_step_bound hT hf hg E hE hb γ n))
  have hpos : 0 < 1-((K : ℝ)*T)^n/n.factorial := sub_pos.mpr hn
  have hh : dist α γ ≤ integratedSensitivity K T n*E/(1-((K : ℝ)*T)^n/n.factorial) :=
    (le_div_iff₀ hpos).mpr (by nlinarith [hd])
  convert hh using 1 <;> ring

end FourPapersCommon
