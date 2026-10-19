-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiniteMaximum
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Genuine iid Gaussian random-energy lower bounds. The occupancy estimate
is a consequence of the actual product Gaussian law, rather than an assumed
random-energy asymptotic. -/

namespace SlowEquilibration.SphericalParisiGaussianREM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def labelCount (γ : ℝ) (N : ℕ) : ℕ := max 1 ⌈Real.exp ((N : ℝ) * γ)⌉₊
def remLogAverage (N k : ℕ) (β : ℝ) (g : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.log ((1 / (k : ℝ)) * ∑ i : Fin k, Real.exp (β * Real.sqrt (N : ℝ) * g i))
def gaussianProduct (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
instance (k : ℕ) : IsProbabilityMeasure (gaussianProduct k) := by
  unfold gaussianProduct
  infer_instance

def occupancy (k : ℕ) (s : Set ℝ) (g : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, s.indicator (fun _ => (1 : ℝ)) (g i)

def gaussianAbsoluteMean : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1

theorem gaussianAbsoluteMean_nonneg : 0 ≤ gaussianAbsoluteMean :=
  integral_nonneg (fun x => abs_nonneg x)

theorem occupancy_measurable (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable (occupancy k s) := by
  unfold occupancy
  exact Finset.measurable_sum _ (fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i))

theorem occupancy_memLp (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    MemLp (occupancy k s) 2 (gaussianProduct k) := by
  unfold occupancy
  apply memLp_finsetSum
  intro i _
  exact (memLp_const (1 : ℝ)).indicator (hs.preimage (measurable_pi_apply i))

theorem occupancy_expectation (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ g, occupancy k s g ∂gaussianProduct k) = (k : ℝ) * (gaussianReal 0 1).real s := by
  unfold occupancy gaussianProduct
  rw [integral_finsetSum]
  · have hcoord (i : Fin k) :
        (∫ g : Fin k → ℝ, s.indicator (fun _ => (1 : ℝ)) (g i)
          ∂Measure.pi (fun _ => gaussianReal 0 1)) = (gaussianReal 0 1).real s := by
      rw [integral_comp_eval (μ := fun _ : Fin k => gaussianReal 0 1)
        (f := s.indicator (fun _ => (1 : ℝ)))
        (measurable_const.indicator hs).aestronglyMeasurable,
        integral_indicator_const 1 hs]
      simp
    simp only [hcoord,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · intro i _
    exact integrable_comp_eval ((integrable_const (1 : ℝ)).indicator hs)

/-- Exact binomial variance of the count under the literal product law. -/
theorem occupancy_variance (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    Var[occupancy k s; gaussianProduct k] =
      (k : ℝ) * (gaussianReal 0 1).real s * (1 - (gaussianReal 0 1).real s) := by
  have hi : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 (gaussianReal 0 1) :=
    (memLp_const 1).indicator hs
  have hv : Var[s.indicator (fun _ => (1 : ℝ)); gaussianReal 0 1] =
      (gaussianReal 0 1).real s * (1 - (gaussianReal 0 1).real s) := by
    rw [variance_eq_sub hi]
    have he : (s.indicator (fun _ => (1 : ℝ))) ^ 2 =
        s.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [he,integral_indicator_const 1 hs]
    simp only [smul_eq_mul,mul_one]
    ring
  have he : occupancy k s = ∑ i : Fin k, fun g => s.indicator (fun _ => (1 : ℝ)) (g i) := by
    funext g
    simp only [occupancy,Finset.sum_apply]
  rw [he]
  unfold gaussianProduct
  rw [variance_sum_pi (fun _ => hi)]
  simp only [hv,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem occupancy_variance_le (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    Var[occupancy k s; gaussianProduct k] ≤ (k : ℝ) * (gaussianReal 0 1).real s := by
  have hi : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 (gaussianReal 0 1) :=
    (memLp_const 1).indicator hs
  have hv : Var[s.indicator (fun _ => (1 : ℝ)); gaussianReal 0 1] ≤
      (gaussianReal 0 1).real s := by
    have h := variance_le_sub_mul_sub (a := 0) (b := 1)
      (μ := gaussianReal 0 1) (X := s.indicator (fun _ => (1 : ℝ)))
      (.of_forall fun x => by by_cases hx : x ∈ s <;> simp [hx])
      (measurable_const.indicator hs).aemeasurable
    rw [integral_indicator_const 1 hs] at h
    simp only [smul_eq_mul, mul_one, sub_zero] at h
    nlinarith [sq_nonneg ((gaussianReal 0 1).real s)]
  have he : occupancy k s = ∑ i : Fin k, fun g => s.indicator (fun _ => (1 : ℝ)) (g i) := by
    funext g
    simp only [occupancy,Finset.sum_apply]
  rw [he]
  unfold gaussianProduct
  rw [variance_sum_pi (fun _ => hi)]
  calc
    _ ≤ ∑ _i : Fin k, (gaussianReal 0 1).real s := Finset.sum_le_sum (fun _ _ => hv)
    _ = _ := by simp

/-- Chebyshev applied to the literal iid Gaussian occupancy count. -/
theorem occupancy_bad_probability (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    (hk : 0 < k) (hp : 0 < (gaussianReal 0 1).real s) :
    (gaussianProduct k).real {g | occupancy k s g < (k : ℝ) * (gaussianReal 0 1).real s / 2}
      ≤ 4 / ((k : ℝ) * (gaussianReal 0 1).real s) := by
  have hc : 0 < (k : ℝ) * (gaussianReal 0 1).real s := mul_pos (Nat.cast_pos.mpr hk) hp
  have hsub : {g | occupancy k s g < (k : ℝ) * (gaussianReal 0 1).real s / 2} ⊆
      {g | (k : ℝ) * (gaussianReal 0 1).real s / 2 ≤
        |occupancy k s g - ∫ z, occupancy k s z ∂gaussianProduct k|} := by
    intro g hg
    change occupancy k s g < (k : ℝ) * (gaussianReal 0 1).real s / 2 at hg
    change (k : ℝ) * (gaussianReal 0 1).real s / 2 ≤
      |occupancy k s g - ∫ z, occupancy k s z ∂gaussianProduct k|
    rw [occupancy_expectation k hs]
    rw [abs_of_neg (by linarith)]
    linarith
  have ht := meas_ge_le_variance_div_sq (occupancy_memLp k hs) (half_pos hc)
  have hReal := ENNReal.toReal_mono (by finiteness) ht
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hReal
  have hv := occupancy_variance_le k hs
  have hbound : Var[occupancy k s; gaussianProduct k] /
      ((k : ℝ) * (gaussianReal 0 1).real s / 2) ^ 2 ≤
      4 / ((k : ℝ) * (gaussianReal 0 1).real s) := by
    apply (div_le_iff₀ (sq_pos_of_pos (half_pos hc))).mpr
    field_simp
    nlinarith
  exact (measureReal_mono hsub).trans (hReal.trans hbound)

/-- A direct lower bound on the true one-dimensional Gaussian interval mass. -/
theorem gaussian_interval_mass_lower {a : ℝ} (ha : 0 ≤ a) :
    (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-((a + 1) ^ 2) / 2) ≤
      (gaussianReal 0 1).real (Icc a (a + 1)) := by
  have hnonneg : 0 ≤ ∫ x in Icc a (a + 1), gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _)
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal hnonneg]
  have hi : IntegrableOn (gaussianPDFReal 0 1) (Icc a (a + 1)) :=
    (integrable_gaussianPDFReal 0 1).restrict
  have hconst : IntegrableOn (fun _ : ℝ =>
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-((a + 1) ^ 2) / 2)) (Icc a (a + 1)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hb := integral_mono_ae hconst hi (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => by
    unfold gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero,one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hh : x ^ 2 ≤ (a + 1) ^ 2 := (sq_le_sq₀ hx0 (by linarith)).mpr hx.2
    linarith))
  simpa only [integral_const, measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ a + 1 - a),
    smul_eq_mul, show a + 1 - a = 1 by ring,ENNReal.ofReal_one,ENNReal.toReal_one,one_mul] using hb

def rawLogAverage (k : ℕ) (α : ℝ) (g : Fin k → ℝ) : ℝ :=
  Real.log ((∑ i : Fin k, Real.exp (α * g i)) / (k : ℝ))

theorem rawLogAverage_measurable (k : ℕ) (α : ℝ) : Measurable (rawLogAverage k α) := by
  unfold rawLogAverage
  fun_prop

theorem rawLogAverage_single_lower (k : ℕ) (hk : 0 < k) (α : ℝ)
    (g : Fin k → ℝ) (i : Fin k) :
    α * g i - Real.log (k : ℝ) ≤ rawLogAverage k α g := by
  have hkc : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : Real.exp (α * g i) ≤ ∑ j : Fin k, Real.exp (α * g j) :=
    Finset.single_le_sum (f := fun j => Real.exp (α * g j)) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have ht := Real.log_le_log (div_pos (Real.exp_pos _) hkc)
    (div_le_div_of_nonneg_right hs hkc.le)
  rw [Real.log_div (Real.exp_pos _).ne' hkc.ne', Real.log_exp] at ht
  exact ht

theorem rawLogAverage_upper (k : ℕ) (hk : 0 < k) {α : ℝ} (hα : 0 ≤ α)
    (g : Fin k → ℝ) : rawLogAverage k α g ≤ α * ∑ i : Fin k, |g i| := by
  have hkc : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let i : Fin k := ⟨0,hk⟩
  have hs : 0 < ∑ j : Fin k, Real.exp (α * g j) :=
    (Real.exp_pos (α * g i)).trans_le (Finset.single_le_sum (f := fun j => Real.exp (α * g j))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i))
  have hb : (∑ j : Fin k, Real.exp (α * g j)) ≤
      (k : ℝ) * Real.exp (α * ∑ j : Fin k, |g j|) := by
    calc
      _ ≤ ∑ _j : Fin k, Real.exp (α * ∑ j : Fin k, |g j|) := by
        apply Finset.sum_le_sum
        intro j _
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hα
        exact (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (g j))
          (Finset.mem_univ j))
      _ = _ := by simp
  have hu : (∑ j : Fin k, Real.exp (α * g j)) / (k : ℝ) ≤
      Real.exp (α * ∑ j : Fin k, |g j|) :=
    (div_le_iff₀ hkc).mpr (by simpa only [mul_comm] using hb)
  have ht := Real.log_le_log (div_pos hs hkc) hu
  simpa only [Real.log_exp,rawLogAverage] using ht

theorem rawLogAverage_integrable (k : ℕ) (hk : 0 < k) {α : ℝ} (hα : 0 ≤ α) :
    Integrable (rawLogAverage k α) (gaussianProduct k) := by
  let i : Fin k := ⟨0,hk⟩
  have hi : Integrable (fun g : Fin k → ℝ => ∑ j : Fin k, |g j|) (gaussianProduct k) := by
    apply integrable_finsetSum
    intro j _
    exact integrable_comp_eval (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs
  apply ((hi.const_mul α).add (integrable_const (Real.log (k : ℝ)))).mono'
    (rawLogAverage_measurable k α).aestronglyMeasurable
  exact .of_forall fun g => by
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    have hc : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
    have hu := rawLogAverage_upper k hk hα g
    have hl := rawLogAverage_single_lower k hk α g i
    have hai : |g i| ≤ ∑ j : Fin k, |g j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ i)
    have hal : -∑ j : Fin k, |g j| ≤ g i := by linarith [neg_abs_le (g i)]
    rw [abs_le]
    constructor
    · nlinarith
    · linarith

theorem rawLogAverage_occupancy_lower (k : ℕ) (hk : 0 < k) {α a p : ℝ}
    (hα : 0 ≤ α) (hp : 0 < p) {s : Set ℝ} (ha : s ⊆ Ici a)
    (g : Fin k → ℝ) (hg : (k : ℝ) * p / 2 ≤ occupancy k s g) :
    α * a + Real.log (p / 2) ≤ rawLogAverage k α g := by
  have hkc : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : Real.exp (α * a) * occupancy k s g ≤ ∑ i : Fin k, Real.exp (α * g i) := by
    unfold occupancy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : g i ∈ s
    · rw [indicator_of_mem hi, mul_one]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ha hi) hα)
    · rw [indicator_of_notMem hi, mul_zero]
      exact (Real.exp_pos _).le
  have hl : Real.exp (α * a) * (p / 2) ≤
      (∑ i : Fin k, Real.exp (α * g i)) / (k : ℝ) := by
    apply (le_div_iff₀ hkc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg (Real.exp_pos (α * a)).le]
  have ht := Real.log_le_log (mul_pos (Real.exp_pos _) (half_pos hp)) hl
  rw [Real.log_mul (Real.exp_pos _).ne' (half_pos hp).ne', Real.log_exp] at ht
  exact ht

/-- Finite expected REM lower bound obtained from true occupancy, its binomial
variance, and a genuine Gaussian coordinate on the exceptional event. -/
theorem expected_rawLogAverage_lower (k : ℕ) (hk : 0 < k) {α a : ℝ}
    (hα : 0 ≤ α) {s : Set ℝ} (hs : MeasurableSet s) (ha : s ⊆ Ici a)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hmass : p₀ ≤ (gaussianReal 0 1).real s) :
    let C := α * a + Real.log (p₀ / 2)
    C - (4 / ((k : ℝ) * p₀)) * (|C| + Real.log (k : ℝ)) - α * gaussianAbsoluteMean ≤
      ∫ g, rawLogAverage k α g ∂gaussianProduct k := by
  dsimp only
  let p := (gaussianReal 0 1).real s
  let C := α * a + Real.log (p₀ / 2)
  have hp : 0 < (gaussianReal 0 1).real s := hp₀.trans_le hmass
  let B : Set (Fin k → ℝ) := {g | occupancy k s g < (k : ℝ) * p / 2}
  let i : Fin k := ⟨0,hk⟩
  have hB : MeasurableSet B := measurableSet_lt (occupancy_measurable k hs) measurable_const
  have hgi : Integrable (fun g : Fin k → ℝ => |g i|) (gaussianProduct k) :=
    integrable_comp_eval (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs
  have hiC : Integrable (Bᶜ.indicator (fun _ => C)) (gaussianProduct k) :=
    (integrable_const C).indicator hB.compl
  have hiK : Integrable (B.indicator (fun _ => -Real.log (k : ℝ))) (gaussianProduct k) :=
    (integrable_const _).indicator hB
  have hi := integral_mono ((hiC.add hiK).sub (hgi.const_mul α))
    (rawLogAverage_integrable k hk hα) (fun g => by
      simp only [Pi.add_apply,Pi.sub_apply]
      by_cases hg : g ∈ B
      · rw [indicator_of_notMem (show g ∉ Bᶜ from not_not.mpr hg), indicator_of_mem hg, zero_add]
        have hl := rawLogAverage_single_lower k hk α g i
        have hh := mul_le_mul_of_nonneg_left (neg_abs_le (g i)) hα
        linarith
      · rw [indicator_of_mem (show g ∈ Bᶜ from hg), indicator_of_notMem hg, add_zero]
        have hl := rawLogAverage_occupancy_lower k hk hα hp ha g (le_of_not_gt hg)
        have hlog := Real.log_le_log (half_pos hp₀) (div_le_div_of_nonneg_right hmass (by norm_num : (0 : ℝ) ≤ 2))
        dsimp [C]
        linarith [mul_nonneg hα (abs_nonneg (g i))])
  rw [integral_sub' (hiC.add hiK) (hgi.const_mul α), integral_add' hiC hiK,
    integral_indicator_const C hB.compl, integral_indicator_const _ hB,
    integral_const_mul, probReal_compl_eq_one_sub hB] at hi
  have habs : (∫ g : Fin k → ℝ, |g i| ∂gaussianProduct k) = gaussianAbsoluteMean := by
    exact integral_comp_eval (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs.aestronglyMeasurable
  rw [habs] at hi
  simp only [smul_eq_mul] at hi
  have hq := (occupancy_bad_probability k hs hk hp).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
      (mul_pos (Nat.cast_pos.mpr hk) hp₀) (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg k)))
  have hc : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hq0 : 0 ≤ (gaussianProduct k).real B := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hq (add_nonneg (abs_nonneg C) hc)
  have hC : C ≤ |C| := le_abs_self C
  have hqc := mul_le_mul_of_nonneg_left hC hq0
  dsimp [C,p,B] at hi hmul hqc ⊢
  nlinarith

theorem labelCount_pos (γ : ℝ) (N : ℕ) : 0 < labelCount γ N :=
  lt_of_lt_of_le (by norm_num : 0 < 1) (le_max_left _ _)

theorem labelCount_exp_lower (γ : ℝ) (N : ℕ) :
    Real.exp ((N : ℝ) * γ) ≤ (labelCount γ N : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈Real.exp ((N : ℝ) * γ)⌉₊)

theorem labelCount_exp_upper {γ : ℝ} (hγ : 0 ≤ γ) (N : ℕ) :
    (labelCount γ N : ℝ) ≤ 2 * Real.exp ((N : ℝ) * γ) := by
  have hc : 1 ≤ ⌈Real.exp ((N : ℝ) * γ)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  rw [labelCount,max_eq_right hc]
  have he : 1 ≤ Real.exp ((N : ℝ) * γ) := Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg N) hγ)
  have hh := (Nat.ceil_lt_add_one ((Real.exp_pos ((N : ℝ) * γ)).le)).le
  linarith

theorem labelCount_log_upper {γ : ℝ} (hγ : 0 ≤ γ) (N : ℕ) :
    Real.log (labelCount γ N : ℝ) ≤ (N : ℝ) * γ + Real.log 2 := by
  have hh := Real.log_le_log (Nat.cast_pos.mpr (labelCount_pos γ N)) (labelCount_exp_upper hγ N)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne',Real.log_exp] at hh
  linarith

theorem inverse_sqrt_dimension_tendsto :
    Tendsto (fun N : ℕ => 1 / Real.sqrt (N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The Gaussian interval probability has its actual quadratic rate. -/
theorem gaussian_interval_mass_eventually {u θ : ℝ} (hu : 0 ≤ u) (hθ : u ^ 2 / 2 < θ) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-(N : ℝ) * θ) ≤
        (gaussianReal 0 1).real (Icc (u * Real.sqrt (N : ℝ)) (u * Real.sqrt (N : ℝ) + 1)) := by
  have hr : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hs : Tendsto (fun N : ℕ => u / Real.sqrt (N : ℝ) +
      (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) / (N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_one_div,mul_zero,zero_add] using
      (inverse_sqrt_dimension_tendsto.const_mul u).add
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2))
  filter_upwards [eventually_ge_atTop 1,hs.eventually (gt_mem_nhds (sub_pos.mpr hθ))] with N hN hsmall
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hNs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq := Real.sq_sqrt hNr.le
  have hqsq : (u * Real.sqrt (N : ℝ)) ^ 2 = u ^ 2 * (N : ℝ) := by rw [mul_pow,hsq]
  have hid : (u * Real.sqrt (N : ℝ) + Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) / (N : ℝ) =
      u / Real.sqrt (N : ℝ) + (Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2) / (N : ℝ) := by
    field_simp
    nlinarith
  have hm : u * Real.sqrt (N : ℝ) + Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2 <
      (θ - u ^ 2 / 2) * (N : ℝ) := (div_lt_iff₀ hNr).mp (by rw [hid]; exact hsmall)
  have hexp : Real.exp (-(N : ℝ) * θ) ≤
      Real.exp (-Real.log (Real.sqrt (2 * Real.pi)) - ((u * Real.sqrt (N : ℝ) + 1) ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hqsq]
  have hidexp : Real.exp (-Real.log (Real.sqrt (2 * Real.pi)) -
      ((u * Real.sqrt (N : ℝ) + 1) ^ 2) / 2) =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-((u * Real.sqrt (N : ℝ) + 1) ^ 2) / 2) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_neg,Real.exp_log hr]
    simp only [one_div,neg_div]
  rw [hidexp] at hexp
  exact hexp.trans (gaussian_interval_mass_lower (mul_nonneg hu (Real.sqrt_nonneg _)))

theorem remLogAverage_measurable (N k : ℕ) (β : ℝ) : Measurable (remLogAverage N k β) := by
  unfold remLogAverage
  exact Real.measurable_log.comp (by fun_prop)

theorem remLogAverage_integrable (N k : ℕ) (hk : 0 < k) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (remLogAverage N k β) (SYK.standardGaussianMeasureOnEuclidean (Fin k)) := by
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [integrable_map_measure (remLogAverage_measurable N k β).aestronglyMeasurable
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.aemeasurable]
  have he : (remLogAverage N k β) ∘ (WithLp.toLp 2) =
      rawLogAverage k (β * Real.sqrt (N : ℝ)) := by
    funext g
    simp [remLogAverage,rawLogAverage,div_eq_inv_mul]
  rw [he]
  exact rawLogAverage_integrable k hk (mul_nonneg hβ (Real.sqrt_nonneg _))

theorem gaussian_rem_integral_eq_product (N k : ℕ) (β : ℝ) :
    (∫ g, remLogAverage N k β g ∂SYK.standardGaussianMeasureOnEuclidean (Fin k)) =
      ∫ g, rawLogAverage k (β * Real.sqrt (N : ℝ)) g ∂gaussianProduct k := by
  unfold SYK.standardGaussianMeasureOnEuclidean gaussianProduct
  rw [integral_map (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.aemeasurable]
  · apply integral_congr_ae
    exact .of_forall fun g => by simp [remLogAverage,rawLogAverage,div_eq_inv_mul]
  · unfold remLogAverage
    apply Measurable.aestronglyMeasurable
    exact Real.measurable_log.comp (by fun_prop)

/-- Lower bound with a slightly enlarged quadratic rate. All measure and
moment hypotheses have already been derived from the true iid Gaussian law. -/
theorem eventual_rem_lower_rate {β u γ θ : ℝ} (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hθ : u ^ 2 / 2 < θ) (hγ : θ < γ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      β * u - θ - ε ≤
        (∫ g, remLogAverage N (labelCount γ N) β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Fin (labelCount γ N))) / (N : ℝ) := by
  have hγ0 : 0 ≤ γ := (by nlinarith [sq_nonneg u] : 0 ≤ θ).trans hγ.le
  let D := |β * u - θ| + γ + 2 * Real.log 2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htail : Tendsto (fun N : ℕ =>
      Real.log 2 / (N : ℝ) + 4 * Real.exp (-(N : ℝ) * (γ - θ)) * D +
      β * gaussianAbsoluteMean / Real.sqrt (N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.mpr hγ))
    simpa only [Function.comp_apply,neg_mul,mul_zero,zero_mul,add_zero,zero_add,mul_one_div] using
      ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add
        ((he.const_mul 4).mul_const D)).add
        (inverse_sqrt_dimension_tendsto.const_mul (β * gaussianAbsoluteMean))
  filter_upwards [eventually_ge_atTop 1,gaussian_interval_mass_eventually hu hθ,
    htail.eventually (gt_mem_nhds hε)] with N hN hmass hsmall
  let k := labelCount γ N
  let α := β * Real.sqrt (N : ℝ)
  let a := u * Real.sqrt (N : ℝ)
  let p := Real.exp (-(N : ℝ) * θ)
  let A := β * u - θ
  have hk : 0 < k := labelCount_pos γ N
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq := Real.sq_sqrt hNr.le
  have hp : 0 < p := Real.exp_pos _
  have hα : 0 ≤ α := mul_nonneg hβ (Real.sqrt_nonneg _)
  have hfinite := expected_rawLogAverage_lower k hk hα measurableSet_Icc
    (show Icc a (a + 1) ⊆ Ici a from fun _ hx => hx.1) hp hmass
  have hC : α * a + Real.log (p / 2) = (N : ℝ) * A - Real.log 2 := by
    dsimp [α,a,p,A]
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0),Real.log_exp]
    have hprod : β * Real.sqrt (N : ℝ) * (u * Real.sqrt (N : ℝ)) = β * u * (N : ℝ) := by
      calc
        _ = β * u * (Real.sqrt (N : ℝ)) ^ 2 := by ring
        _ = _ := by rw [hsq]
    rw [hprod]
    ring
  rw [hC] at hfinite
  have hkexp := labelCount_exp_lower γ N
  have hden : Real.exp ((N : ℝ) * (γ - θ)) ≤ (k : ℝ) * p := by
    have ht := mul_le_mul_of_nonneg_right hkexp hp.le
    dsimp [p,k] at ht ⊢
    rw [← Real.exp_add] at ht
    convert ht using 1
    congr 1
    ring
  have hq : 4 / ((k : ℝ) * p) ≤ 4 * Real.exp (-(N : ℝ) * (γ - θ)) := by
    have ht := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _) hden
    simpa only [div_eq_mul_inv,← Real.exp_neg,neg_mul] using ht
  have hkc : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hku := labelCount_log_upper hγ0 N
  have habs : |(N : ℝ) * A - Real.log 2| + Real.log (k : ℝ) ≤ (N : ℝ) * D := by
    have hh := abs_sub ((N : ℝ) * A) (Real.log 2)
    rw [abs_mul,abs_of_pos hNr,abs_of_nonneg hlog2] at hh
    have hlog := mul_le_mul_of_nonneg_left hNr1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog2)
    dsimp [D,A,k] at hh hku ⊢
    nlinarith
  have herr : (4 / ((k : ℝ) * p)) *
      (|(N : ℝ) * A - Real.log 2| + Real.log (k : ℝ)) ≤
      (N : ℝ) * (4 * Real.exp (-(N : ℝ) * (γ - θ)) * D) := by
    calc
      _ ≤ (4 * Real.exp (-(N : ℝ) * (γ - θ))) *
          (|(N : ℝ) * A - Real.log 2| + Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hq (add_nonneg (abs_nonneg _) hkc)
      _ ≤ (4 * Real.exp (-(N : ℝ) * (γ - θ))) * ((N : ℝ) * D) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ = _ := by ring
  have hroot : α * gaussianAbsoluteMean = (N : ℝ) *
      (β * gaussianAbsoluteMean / Real.sqrt (N : ℝ)) := by
    dsimp [α]
    field_simp
    rw [hsq]
    ring
  rw [gaussian_rem_integral_eq_product]
  apply (le_div_iff₀ hNr).mpr
  rw [hroot] at hfinite
  dsimp [A] at hfinite herr
  have hsmallmul := mul_lt_mul_of_pos_left hsmall hNr
  have hdiv : (N : ℝ) * (Real.log 2 / (N : ℝ)) = Real.log 2 := by
    field_simp
  rw [mul_add,mul_add,hdiv] at hsmallmul
  nlinarith

/-- Genuine iid Gaussian REM expected log-average lower asymptotic. -/
theorem eventual_rem_lower {β u γ : ℝ} (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hγ : u ^ 2 / 2 < γ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      β * u - u ^ 2 / 2 - ε ≤
        (∫ g, remLogAverage N (labelCount γ N) β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Fin (labelCount γ N))) / (N : ℝ) := by
  let d := min ((γ - u ^ 2 / 2) / 2) (ε / 2)
  have hd : 0 < d := lt_min (half_pos (sub_pos.mpr hγ)) (half_pos hε)
  have hdγ : d ≤ (γ - u ^ 2 / 2) / 2 := min_le_left _ _
  have hdε : d ≤ ε / 2 := min_le_right _ _
  have hθ : u ^ 2 / 2 < u ^ 2 / 2 + d := by linarith
  have hθγ : u ^ 2 / 2 + d < γ := by linarith
  filter_upwards [eventual_rem_lower_rate hβ hu hθ hθγ (ε / 2) (half_pos hε)] with N hN
  linarith

end
end SlowEquilibration.SphericalParisiGaussianREM
