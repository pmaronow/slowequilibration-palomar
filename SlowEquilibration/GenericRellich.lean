-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
-- Modifications: arbitrary dimension; independent coordinate calculus;
-- irrelevant jet/geometry dependencies removed; Lean 4.35 public modules.
module

public import Mathlib

@[expose] public section

/-!
# Dimension-generic cube Rellich compactness

This is a dimension-generic adaptation of the actual Lebesgue cube proof in
openai/math, at the commit requested by the user. Every source fragment below
records its origin. The proof uses the one-dimensional fundamental theorem,
Cauchy--Schwarz, tensorized Poincare, the finite-cell integral partition and
countable diagonal compactness of the genuine cell means.
-/
namespace SlowEquilibration.GenericRellich

open MeasureTheory Set Function Metric Filter
open scoped ContDiff Topology
noncomputable section

/-- The actual coordinate directional derivative in the standard product basis. -/
def coordPartial {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

lemma real_coordPartial_smooth {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (fun x => coordPartial f x i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealIntegralSquare.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
lemma real_integral_square_le {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (hm : 0 < mu.real univ) (f : X → ℝ) (hf : Integrable f mu)
    (hf2 : Integrable (fun x ↦ f x^2) mu) :
    (∫ x, f x ∂mu)^2 ≤ mu.real univ*(∫ x, f x^2 ∂mu) := by
  let m := mu.real univ
  let localIndex := ∫ x, f x ∂mu
  let q := localIndex/m
  have hq : m*q=localIndex := mul_div_cancel₀ localIndex hm.ne'
  have he : (fun x ↦ (f x-q)^2) = fun x ↦ (f x^2-(2*q)*f x)+q^2 := by
    funext x
    ring
  have hnonneg : 0 ≤ ∫ x, (f x-q)^2 ∂mu := integral_nonneg (fun x ↦ sq_nonneg (f x-q))
  have hsub : Integrable (fun x ↦ f x^2-(2*q)*f x) mu := hf2.sub (hf.const_mul _)
  rw [he,integral_add hsub (integrable_const _),
    integral_sub hf2 (hf.const_mul _),integral_const_mul,integral_const] at hnonneg
  change 0 ≤ (∫ x, f x^2 ∂mu)-(2*q)*localIndex+m*q^2 at hnonneg
  have hmul := mul_nonneg hm.le hnonneg
  have hpoly : m*((∫ x, f x^2 ∂mu)-(2*q)*localIndex+m*q^2) =
      m*(∫ x, f x^2 ∂mu)-localIndex^2 := by
    calc
      _ = m*(∫ x, f x^2 ∂mu)-2*(m*q)*localIndex+(m*q)^2 := by ring
      _ = _ := by rw [hq]; ring
  rw [hpoly] at hmul
  exact sub_nonneg.mp hmul

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealMeanSquareDecomposition.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_mean_square_decomposition {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu)
    (c : ℝ) :
    (∫ x, (f x-c)^2 ∂mu) =
      (∫ x, (f x-(∫ y, f y ∂mu)/mu.real univ)^2 ∂mu) +
        mu.real univ*((∫ y, f y ∂mu)/mu.real univ-c)^2 := by
  have hexpand (d : ℝ) : (∫ x, (f x-d)^2 ∂mu) =
      (∫ x, f x^2 ∂mu)-2*d*(∫ x, f x ∂mu)+mu.real univ*d^2 := by
    have he : (fun x ↦ (f x-d)^2) = fun x ↦ (f x^2-(2*d)*f x)+d^2 := by
      funext x; ring
    have hs : Integrable (fun x ↦ f x^2-(2*d)*f x) mu := hf2.sub (hf.const_mul _)
    rw [he,integral_add hs (integrable_const _),
      integral_sub hf2 (hf.const_mul (2*d)),integral_const_mul,integral_const]
    rfl
  rw [hexpand,hexpand]
  field_simp
  ring

theorem real_mean_square_contraction {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu) :
    mu.real univ*((∫ x, f x ∂mu)/mu.real univ)^2 ≤ ∫ x, f x^2 ∂mu := by
  have h := real_integral_square_le mu hm f hf hf2
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    _ = (∫ x, f x ∂mu)^2 := by field_simp
    _ ≤ _ := by simpa [mul_comm] using h

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealFinCubeFubini.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
def realFinCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi (fun _ ↦ Icc (-1:ℝ) 1)

lemma realFinCube_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (realFinCube n) =
      Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (-1:ℝ) 1)) :=
  Measure.restrict_pi_pi _ _

lemma realFinCube_integrable (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    IntegrableOn F (realFinCube n) :=
  hF.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ ↦ isCompact_Icc))

theorem realFinCube_integral_succ (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ)
    (hF : Continuous F) :
    (∫ z in realFinCube (n+1), F z) =
      ∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (Fin.cons t z) := by
  have hi := realFinCube_integrable (n+1) F hF
  rw [IntegrableOn,realFinCube_volume] at hi
  let μ := fun _ : Fin (n+1) ↦ volume.restrict (Icc (-1:ℝ) 1)
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm
  have hh := hm.integrable_comp_of_integrable hi
  have he := hm.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero] at hh he
  simp only [realFinCube_volume]
  exact he.symm.trans (integral_prod _ hh)

lemma realFinCube_integral_zero (F : (Fin 0 → ℝ) → ℝ) :
    (∫ z in realFinCube 0, F z) = F Fin.elim0 := by
  have hs : realFinCube 0 = univ := by ext z; simp [realFinCube]
  rw [hs,Measure.restrict_univ,Measure.volume_pi_eq_dirac Fin.elim0,integral_dirac]

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeL2EmbeddingLemmas.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
lemma realFinCube_isCompact (n : ℕ) : IsCompact (realFinCube n) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

lemma realFinCube_mass (n : ℕ) :
    (volume.restrict (realFinCube n)).real univ = (2:ℝ)^n := by
  rw [realFinCube_volume,Measure.real,Measure.pi_univ]
  norm_num

lemma real_interval_cube_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun t ↦ ∫ z in realFinCube n, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ (realFinCube_isCompact n)
  exact hF

lemma real_cube_interval_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z ↦ ∫ t in Icc (-1:ℝ) 1, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hF.comp continuous_swap

lemma real_interval_cube_integral_swap (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z)) =
      ∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, F (t,z) := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod (realFinCube_isCompact n))

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealFinCubeSlices.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
lemma real_finCons_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.1))
  · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp
      (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.2))

lemma real_finCube_slice_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun z ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_const.prodMk contDiff_id))

lemma real_finCube_line_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun t ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_id.prodMk contDiff_const))

lemma real_coordPartial_eq_deriv_update (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) (i : Fin n) :
    coordPartial W z i = deriv (fun t ↦ W (update z i t)) (z i) := by
  have hd := (hW.differentiable (by simp) (update z i (z i))).hasFDerivAt.comp_hasDerivAt
    (z i) (hasDerivAt_update z i (z i))
  simpa [coordPartial,Function.comp_def] using hd.deriv.symm

lemma real_finCube_slice_partial (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    coordPartial (fun y ↦ W (Fin.cons t y)) z i =
      coordPartial W (Fin.cons t z) i.succ := by
  rw [real_coordPartial_eq_deriv_update n _ (real_finCube_slice_smooth n W hW t),
    real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : (Fin.cons t (update z i s) : Fin (n+1) → ℝ) =
      update (Fin.cons t z : Fin (n+1) → ℝ) i.succ s := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [Ne.symm (Fin.succ_ne_zero i)]
    · by_cases h : k=i
      · subst k; simp
      · simp [h]
  simp only [he,Fin.cons_succ]

lemma real_finCube_line_deriv (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) :
    deriv (fun s ↦ W (Fin.cons s z)) t = coordPartial W (Fin.cons t z) 0 := by
  rw [real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : update (Fin.cons t z : Fin (n+1) → ℝ) 0 s = Fin.cons s z := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
  simp only [he,Fin.cons_zero]

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealIntervalDerivativeControl.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
lemma real_interval_integral_square_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, f x)^2 ≤ (b-a)*(∫ x in Icc a b, f x^2) := by
  have hm : (volume.restrict (Icc a b)).real univ=b-a := by simp [hab.le]
  have hpos : 0 < (volume.restrict (Icc a b)).real univ := by rw [hm]; linarith
  have h := real_integral_square_le (volume.restrict (Icc a b)) hpos f
    hf.continuousOn.integrableOn_Icc (hf.pow 2).continuousOn.integrableOn_Icc
  rwa [hm] at h

lemma real_interval_derivative_control (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f x-f y)^2 ≤ (b-a)*(∫ t in Icc a b, (deriv f t)^2) := by
  have hd : Continuous (fun t ↦ |deriv f t|) := (hf.continuous_deriv (by simp)).abs
  have hordered (c d : ℝ) (hc : c ∈ Icc a b) (hd' : d ∈ Icc a b) (hcd : c ≤ d) :
      |f d-f c| ≤ ∫ t in Icc a b, |deriv f t| := by
    have hh := norm_sub_le_integral_of_norm_deriv_le_of_le hcd hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ by rw [Real.norm_eq_abs])) (hd.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at hh
    have hmono : (∫ t in Ioc c d, |deriv f t|) ≤ ∫ t in Icc a b, |deriv f t| := by
      apply setIntegral_mono_set hd.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall (fun t ↦ abs_nonneg (deriv f t)))
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd'.2⟩)
    exact (show |f d-f c| ≤ ∫ t in Ioc c d, |deriv f t| by simpa only [Real.norm_eq_abs] using hh).trans hmono
  have hvar : |f x-f y| ≤ ∫ t in Icc a b, |deriv f t| := by
    rcases le_total y x with h | h
    · exact hordered y x hy hx h
    · simpa only [abs_sub_comm] using hordered x y hx hy h
  have hsq := real_interval_integral_square_le (fun t ↦ |deriv f t|) hd hab
  simp only [sq_abs] at hsq
  have hn : 0 ≤ ∫ t in Icc a b, |deriv f t| := integral_nonneg (fun t ↦ abs_nonneg _)
  have hh := sq_le_sq₀ (abs_nonneg (f x-f y)) hn |>.mpr hvar
  rw [sq_abs] at hh
  exact hh.trans hsq

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealIntervalPoincare.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_interval_poincare (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, (f x-(∫ y in Icc a b, f y)/(b-a))^2) ≤
      (b-a)^2*(∫ x in Icc a b, (deriv f x)^2) := by
  let L := b-a
  let c := (∫ y in Icc a b, f y)/L
  let D := ∫ x in Icc a b, (deriv f x)^2
  have hL : 0 < L := sub_pos.mpr hab
  have hm : (volume.restrict (Icc a b)).real univ=L := by
    simp [hab.le,L]
  have hpt (x : ℝ) (hx : x ∈ Icc a b) : (f x-c)^2 ≤ L*D := by
    have hdiff : (∫ y in Icc a b, f x-f y) = L*(f x-c) := by
      rw [integral_sub (integrable_const _) hf.continuous.continuousOn.integrableOn_Icc,integral_const]
      change (volume.restrict (Icc a b)).real univ*f x-(∫ y in Icc a b, f y) = L*(f x-c)
      rw [hm]
      dsimp [c]
      field_simp
    have hcs := real_interval_integral_square_le (fun y ↦ f x-f y) (continuous_const.sub hf.continuous) hab
    rw [hdiff] at hcs
    have hbound := setIntegral_mono_on (μ := volume)
      ((continuous_const.sub hf.continuous).pow 2).continuousOn.integrableOn_Icc
      (integrable_const (L*D)) measurableSet_Icc
      (fun y hy ↦ real_interval_derivative_control f hf hab x y hx hy)
    rw [integral_const] at hbound
    change (∫ y in Icc a b, (f x-f y)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hbound
    rw [hm] at hbound
    have hh := hcs.trans (mul_le_mul_of_nonneg_left hbound hL.le)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
    nlinarith [hh]
  have hfinal := setIntegral_mono_on (μ := volume) ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc
    (integrable_const (L*D)) measurableSet_Icc hpt
  rw [integral_const] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hfinal
  rw [hm] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ L^2*D
  nlinarith [hfinal]

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeVarianceTensorization.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_interval_cube_variance_le (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, ∫ y in realFinCube n, F (s,y))/(2*2^n))^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ y in realFinCube n, F (t,y))/2^n)^2) +
    (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, F (s,z))/2)^2) := by
  let m : ℝ := 2^n
  have hm : 0 < m := pow_pos (by norm_num) n
  let : IsFiniteMeasure (volume.restrict (realFinCube n)) :=
    isFiniteMeasure_restrict.mpr (realFinCube_isCompact n).measure_ne_top
  let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/m
  let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
  let M : ℝ := (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z))/(2*m)
  have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const m
  have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const 2
  have hmean : (∫ z in realFinCube n, C z)/m = M := by
    dsimp [C,M]
    rw [integral_div,← real_interval_cube_integral_swap n F hF]
    ring
  have hFC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
    (hF.sub (hC.comp continuous_snd)).pow 2
  have hFR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
    (hF.sub (hR.comp continuous_fst)).pow 2
  have hFM : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-M)^2) :=
    (hF.sub continuous_const).pow 2
  have hpt (t : ℝ) : m*(R t-M)^2 ≤ ∫ z in realFinCube n, (F (t,z)-C z)^2 := by
    have hc : Continuous (fun z ↦ F (t,z)-C z) :=
      (hF.comp (continuous_const.prodMk continuous_id)).sub hC
    have h := real_mean_square_contraction (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2))
    have hi : IntegrableOn (fun z ↦ F (t,z)) (realFinCube n) :=
      realFinCube_integrable n _ (hF.comp (continuous_const.prodMk continuous_id))
    rw [realFinCube_mass,integral_sub hi
      (realFinCube_integrable n _ hC),sub_div,hmean] at h
    exact h
  have hbound := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
    (((continuous_const : Continuous (fun _ : ℝ ↦ m)).mul
      ((hR.sub (continuous_const : Continuous (fun _ : ℝ ↦ M))).pow 2)).continuousOn.integrableOn_Icc)
    ((real_interval_cube_integral_continuous n _ hFC).continuousOn.integrableOn_Icc)
    measurableSet_Icc (fun t _ ↦ hpt t)
  have hdecomp (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-M)^2) =
      (∫ z in realFinCube n, (F (t,z)-R t)^2)+m*(R t-M)^2 := by
    have hc : Continuous (fun z : Fin n → ℝ ↦ F (t,z)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have h := real_mean_square_decomposition (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2)) M
    simpa only [realFinCube_mass] using h
  change (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-M)^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-R t)^2)+
      (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2)
  simp_rw [hdecomp]
  have hiR : IntegrableOn (fun t ↦ ∫ z in realFinCube n, (F (t,z)-R t)^2)
      (Icc (-1:ℝ) 1) :=
    (real_interval_cube_integral_continuous n _ hFR).continuousOn.integrableOn_Icc
  have hiM : IntegrableOn (fun t ↦ m*(R t-M)^2) (Icc (-1:ℝ) 1) :=
    (continuous_const.mul ((hR.sub continuous_const).pow 2)).continuousOn.integrableOn_Icc
  rw [integral_add hiR hiM]
  exact add_le_add le_rfl (hbound.trans_eq (real_interval_cube_integral_swap n _ hFC))

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealFinCubePoincare.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_finCube_poincare (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube n, (W x-(∫ y in realFinCube n, W y)/2^n)^2) ≤
      4*(∫ x in realFinCube n, ∑ i, (coordPartial W x i)^2) := by
  induction n with
  | zero => simp [realFinCube_integral_zero]
  | succ n ih =>
    let F : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ W (Fin.cons p.1 p.2)
    have hF : Continuous F := hW.continuous.comp (real_finCons_smooth n).continuous
    let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/2^n
    let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
    have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const _
    have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const _
    have hVR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
      (hF.sub (hR.comp continuous_fst)).pow 2
    have hVC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
      (hF.sub (hC.comp continuous_snd)).pow 2
    let E0 : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ (coordPartial W (Fin.cons p.1 p.2) 0)^2
    let ET : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ ∑ i : Fin n,
      (coordPartial W (Fin.cons p.1 p.2) i.succ)^2
    have hE0 : Continuous E0 :=
      ((real_coordPartial_smooth W hW 0).continuous.comp (real_finCons_smooth n).continuous).pow 2
    have hET : Continuous ET := continuous_finsetSum _ (fun i _ ↦
      ((real_coordPartial_smooth W hW i.succ).continuous.comp (real_finCons_smooth n).continuous).pow 2)
    have htail (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-R t)^2) ≤
        4*(∫ z in realFinCube n, ET (t,z)) := by
      have h := ih (fun z ↦ W (Fin.cons t z)) (real_finCube_slice_smooth n W hW t)
      simpa only [real_finCube_slice_partial n W hW] using h
    have hhead (z : Fin n → ℝ) : (∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2) ≤
        4*(∫ t in Icc (-1:ℝ) 1, E0 (t,z)) := by
      have h := real_interval_poincare (fun t ↦ W (Fin.cons t z))
        (real_finCube_line_smooth n W hW z) (by norm_num : (-1:ℝ)<1)
      simp only [real_finCube_line_deriv n W hW] at h
      norm_num at h
      exact h
    have ht := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
      ((real_interval_cube_integral_continuous n _ hVR).continuousOn.integrableOn_Icc)
      (((real_interval_cube_integral_continuous n ET hET).const_mul 4).continuousOn.integrableOn_Icc)
      measurableSet_Icc (fun t _ ↦ htail t)
    have hh := setIntegral_mono_on (μ := volume)
      (realFinCube_integrable n _ (real_cube_interval_integral_continuous n _ hVC))
      (realFinCube_integrable n _ ((real_cube_interval_integral_continuous n E0 hE0).const_mul 4))
      (realFinCube_isCompact n).measurableSet (fun z _ ↦ hhead z)
    rw [integral_const_mul] at ht hh
    have hvar := (real_interval_cube_variance_le n F hF).trans (add_le_add ht hh)
    rw [← real_interval_cube_integral_swap n E0 hE0] at hvar
    have he (t : ℝ) : (∫ z in realFinCube n, ∑ i : Fin (n+1),
        (coordPartial W (Fin.cons t z) i)^2) =
        (∫ z in realFinCube n, E0 (t,z))+(∫ z in realFinCube n, ET (t,z)) := by
      simp_rw [Fin.sum_univ_succ]
      exact integral_add
        (realFinCube_integrable n _ (hE0.comp (continuous_const.prodMk continuous_id)))
        (realFinCube_integrable n _ (hET.comp (continuous_const.prodMk continuous_id)))
    have hWC : Continuous (fun x ↦ (W x-(∫ y in realFinCube (n+1), W y)/2^(n+1))^2) :=
      (hW.continuous.sub continuous_const).pow 2
    have hWE : Continuous (fun x ↦ ∑ i, (coordPartial W x i)^2) :=
      continuous_finsetSum _ (fun i _ ↦ (real_coordPartial_smooth W hW i).continuous.pow 2)
    rw [realFinCube_integral_succ n _ hWC,
      realFinCube_integral_succ n W hW.continuous,
      realFinCube_integral_succ n _ hWE]
    simp_rw [he]
    rw [integral_add
      ((real_interval_cube_integral_continuous n E0 hE0).continuousOn.integrableOn_Icc)
      ((real_interval_cube_integral_continuous n ET hET).continuousOn.integrableOn_Icc)]
    rw [show (2:ℝ)^(n+1)=2*2^n by rw [pow_succ]; ring]
    calc
      _ ≤ 4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, ET (t,z))+
          4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, E0 (t,z)) := hvar
      _ = _ := by ring

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealScaledCubeIntegration.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
def realScaledCube (n : ℕ) (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  (fun x ↦ c+r • x) '' realFinCube n

lemma realScaledCube_isCompact (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    IsCompact (realScaledCube n c r) :=
  (realFinCube_isCompact n).image (continuous_const.add (continuous_id.const_smul r))

lemma realScaledCube_integral (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (F : (Fin n → ℝ) → ℝ) :
    (∫ y in realScaledCube n c r, F y) = r^n*(∫ x in realFinCube n, F (c+r • x)) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd (x : Fin n → ℝ) : HasFDerivAt (fun y ↦ c+r • y) L x :=
    L.hasFDerivAt.const_add c
  have hi : Injective (fun x : Fin n → ℝ ↦ c+r • x) := by
    intro x y h
    exact (smul_right_injective (Fin n → ℝ) hr.ne') (add_left_cancel h)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (realFinCube_isCompact n).measurableSet (fun x _ ↦ (hd x).hasFDerivWithinAt) hi.injOn F
  have hdet : |L.det|=r^n := by
    simp [L,ContinuousLinearMap.det,LinearMap.det_smul,abs_of_pos hr]
  simpa only [realScaledCube,hdet,smul_eq_mul,integral_const_mul] using h

lemma realScaledCube_eq_closedBall (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    realScaledCube n c r = closedBall c r := by
  have hunit : realFinCube n = closedBall (0 : Fin n → ℝ) 1 := by
    rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
    simp [realFinCube,Real.closedBall_eq_Icc]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [hunit,mem_closedBall,dist_zero_right] at hx
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  · intro hy
    refine ⟨r⁻¹ • (y-c),?_,?_⟩
    · rw [hunit,mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have h : ‖y-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)).trans_eq
        (inv_mul_cancel₀ hr.ne')
    · dsimp
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]

lemma realScaledCube_mass (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    (volume.restrict (realScaledCube n c r)).real univ = (2*r)^n := by
  have h := realScaledCube_integral n c hr (fun _ ↦ (1:ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,one_mul,realFinCube_mass,mul_pow,mul_comm] using h

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealScaledCubePoincare.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
lemma real_affine_coordPartial (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    coordPartial (fun y ↦ W (c+r • y)) x i = r*coordPartial W (c+r • x) i := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd : HasFDerivAt (fun y ↦ c+r • y) L x := L.hasFDerivAt.const_add c
  have h := ((hW.differentiable (by simp) (c+r • x)).hasFDerivAt.comp x hd).fderiv
  simp only [Function.comp_def] at h
  simp [coordPartial,h,L]

theorem real_scaledCube_poincare (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (W : (Fin n → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realScaledCube n c r,
      (W x-(∫ y in realScaledCube n c r, W y)/(2*r)^n)^2) ≤
      4*r^2*(∫ x in realScaledCube n c r, ∑ i, (coordPartial W x i)^2) := by
  have hm : (∫ y in realScaledCube n c r, W y)/(2*r)^n =
      (∫ y in realFinCube n, W (c+r • y))/2^n := by
    rw [realScaledCube_integral n c hr,mul_pow]
    field_simp
  have h := real_finCube_poincare n (fun x ↦ W (c+r • x))
    (hW.comp (contDiff_const.add (contDiff_id.const_smul r)))
  simp_rw [real_affine_coordPartial n W hW,mul_pow,← Finset.mul_sum] at h
  rw [integral_const_mul] at h
  rw [hm,realScaledCube_integral n c hr,realScaledCube_integral n c hr]
  calc
    _ ≤ r^n*(4*(r^2*(∫ x in realFinCube n, ∑ i, (coordPartial W (c+r • x) i)^2))) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hr.le n)
    _ = _ := by ring

theorem real_scaledCube_poincare_integrable (n : ℕ) (c : Fin n → ℝ) (r : ℝ)
    (W : (Fin n → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    IntegrableOn (fun x ↦ (W x-(∫ y in realScaledCube n c r, W y)/(2*r)^n)^2)
      (realScaledCube n c r) ∧
    IntegrableOn (fun x ↦ ∑ i, (coordPartial W x i)^2) (realScaledCube n c r) := by
  constructor
  · exact ((hW.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (realScaledCube_isCompact n c r)
  · apply ContinuousOn.integrableOn_compact (realScaledCube_isCompact n c r)
    exact (continuous_finsetSum _ (fun i _ ↦ (real_coordPartial_smooth W hW i).continuous.pow 2)).continuousOn

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCountableScalarCompactness.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_countable_bounded_subsequence {localIndex : Type*} [Countable localIndex]
    (a : ℕ → localIndex → ℝ) (B : localIndex → ℝ) (hb : ∀ j i, |a j i| ≤ B i) :
    ∃ f : localIndex → ℝ, ∃ nu : ℕ → ℕ, StrictMono nu ∧
      ∀ i, Tendsto (fun j ↦ a (nu j) i) atTop (𝓝 (f i)) := by
  have hc : IsCompact (univ.pi (fun i ↦ Icc (-B i) (B i))) :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hmem (j : ℕ) : a j ∈ univ.pi (fun i ↦ Icc (-B i) (B i)) := by
    intro i _
    exact abs_le.mp (hb j i)
  obtain ⟨f,_,nu,hnu,ht⟩ := hc.tendsto_subseq hmem
  exact ⟨f,nu,hnu,fun i ↦ ((continuous_apply i).tendsto f).comp ht⟩

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealFiniteWeightedCauchy.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_finite_weighted_cauchy {localIndex : Type*} [Fintype localIndex]
    (a : ℕ → localIndex → ℝ) (f w : localIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (f i))) :
    ∀ eps > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      (∑ k, w k*(a i k-a j k)^2) < eps := by
  classical
  let S : ℕ → ℝ := fun j ↦ ∑ k, w k*(a j k-f k)^2
  have ht : Tendsto S atTop (𝓝 0) := by
    have h : Tendsto S atTop (𝓝 (∑ k, w k*(f k-f k)^2)) :=
      tendsto_finsetSum (Finset.univ : Finset localIndex) (fun k _ ↦
      tendsto_const_nhds.mul (((ha k).sub tendsto_const_nhds).pow 2))
    simpa only [sub_self,zero_pow (by decide : 2≠0),mul_zero,Finset.sum_const_zero] using h
  intro eps heps
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_lt_const (show 0 < eps/4 by linarith))
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have hb : (∑ k, w k*(a i k-a j k)^2) ≤ 2*(S i+S j) := by
    dsimp [S]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hsq : (a i k-a j k)^2 ≤ 2*((a i k-f k)^2+(a j k-f k)^2) := by
      nlinarith [sq_nonneg (a i k+a j k-2*f k)]
    calc
      _ ≤ w k*(2*((a i k-f k)^2+(a j k-f k)^2)) := mul_le_mul_of_nonneg_left hsq (hw k)
      _ = _ := by ring
  exact hb.trans_lt (by linarith [hN i hi,hN j hj])

variable {d : ℕ} [NeZero d]

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/CorrugationCubePartition.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
def corrugationCubeCenter (o : (Fin d → ℝ)) (L : ℝ) (n : ℕ) (k : Fin d → Fin n) : (Fin d → ℝ) :=
  fun i ↦ o i + (L/(n:ℝ))*((k i:ℝ)+1/2)

omit [NeZero d] in
lemma corrugationCubeCenter_mem (o : (Fin d → ℝ)) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    corrugationCubeCenter o L n k ∈ Set.Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  constructor <;> intro i
  · dsimp [corrugationCubeCenter]
    have hk : (0:ℝ) ≤ (k i:ℝ) := by positivity
    nlinarith
  · dsimp [corrugationCubeCenter]
    have hk : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

omit [NeZero d] in
lemma corrugationCube_ball_inside (o : (Fin d → ℝ)) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆
      interior (Set.Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  rw [← pi_univ_Icc,interior_pi_set Set.finite_univ]
  intro i _
  change x i ∈ interior (Icc (o i) (o i+L))
  rw [interior_Icc]
  constructor
  all_goals
    have hxi : |x i-corrugationCubeCenter o L n k i| < (L/(n:ℝ))/2 := by
      have hnorm := norm_le_pi_norm (x-corrugationCubeCenter o L n k) i
      exact lt_of_le_of_lt hnorm (by simpa [dist_eq_norm] using hx)
    have ha := abs_lt.mp hxi
    dsimp [corrugationCubeCenter] at ha
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

omit [NeZero d] in
lemma corrugationCube_balls_disjoint (o : (Fin d → ℝ)) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin d → Fin n) (hkj : k ≠ j) :
    Disjoint (ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
      (ball (corrugationCubeCenter o L n j) ((L/(n:ℝ))/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ j i := Function.ne_iff.mp hkj
  have hi' : (k i).val ≠ (j i).val := fun h ↦ hi (Fin.ext h)
  have hd : (1:ℝ) ≤ |(k i:ℝ)-(j i:ℝ)| := by
    rcases lt_or_gt_of_ne hi' with h | h
    · have hh : (k i:ℝ)+1 ≤ (j i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j i:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  apply ball_disjoint_ball
  have hcoord := norm_le_pi_norm (corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i
  have he : ‖(corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i‖ =
      (L/(n:ℝ))*|(k i:ℝ)-(j i:ℝ)| := by
    change |(o i+_)-(o i+_)| = _
    rw [add_sub_add_left_eq_sub,← mul_sub,abs_mul,abs_of_pos hR]
    congr 2
    ring
  rw [he] at hcoord
  rw [dist_eq_norm]
  nlinarith

lemma unit_interval_subdivision {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∃ k : Fin n, (k:ℝ) ≤ t ∧ t ≤ (k:ℝ)+1 := by
  by_cases he : t = n
  · refine ⟨⟨n-1,by omega⟩,?_,?_⟩
    all_goals
      have hn1 : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
      change _ ≤ _
      rw [he]
      linarith
  · have ht : t < n := lt_of_le_of_ne htn he
    let k : ℕ := ⌊t⌋₊
    have hk0 : (k:ℝ) ≤ t := Nat.floor_le ht0
    have hk1 : t < (k:ℝ)+1 := Nat.lt_floor_add_one t
    have hkn : k < n := by exact_mod_cast (hk0.trans_lt ht)
    exact ⟨⟨k,hkn⟩,hk0,hk1.le⟩

omit [NeZero d] in
lemma corrugationCube_closed_cover (o : (Fin d → ℝ)) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (x : (Fin d → ℝ)) (hx : x ∈ Set.Icc o (fun i ↦ o i+L)) :
    ∃ k : Fin d → Fin n,
      x ∈ closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  have hk : ∀ i : Fin d, ∃ k : Fin n,
      (k:ℝ) ≤ (x i-o i)/(L/(n:ℝ)) ∧ (x i-o i)/(L/(n:ℝ)) ≤ (k:ℝ)+1 := by
    intro i
    apply unit_interval_subdivision hn
    · exact div_nonneg (sub_nonneg.mpr (hx.1 i)) hR.le
    · apply (div_le_iff₀ hR).mpr
      have hi := hx.2 i
      nlinarith
  choose k hk using hk
  refine ⟨k,?_⟩
  rw [mem_closedBall,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (L/(n:ℝ))/2)).mpr
  intro i
  have hlo := (le_div_iff₀ hR).mp (hk i).1
  have hhi := (div_le_iff₀ hR).mp (hk i).2
  change |x i-(o i+(L/(n:ℝ))*((k i:ℝ)+1/2))| ≤ _
  rw [abs_le]
  constructor <;> nlinarith

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeCellPartition.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
def realCubeCell (n : ℕ) (k : Fin d → Fin n) : Set (Fin d → ℝ) :=
  realScaledCube d (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (1/(n:ℝ))

omit [NeZero d] in
lemma realCubeCell_closedBall {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    realCubeCell n k = closedBall (corrugationCubeCenter (fun _ ↦ -1) 2 n k) ((2/(n:ℝ))/2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell,realScaledCube_eq_closedBall d _ (div_pos zero_lt_one hnR)]
  congr 1
  ring

omit [NeZero d] in
lemma realCubeCell_isCompact (n : ℕ) (k : Fin d → Fin n) : IsCompact (realCubeCell n k) :=
  realScaledCube_isCompact d _ _

omit [NeZero d] in
lemma realCubeCell_subset {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    realCubeCell n k ⊆ realFinCube d := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell_closedBall hn k,← closure_ball _ (by positivity : (2/(n:ℝ))/2 ≠ 0)]
  have hb := (corrugationCube_ball_inside (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k).trans
    interior_subset
  have he : Icc (fun _ : Fin d ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) = realFinCube d := by
    norm_num [realFinCube]
  rw [he] at hb
  exact closure_minimal hb (realFinCube_isCompact d).isClosed

omit [NeZero d] in
theorem realCubeCell_cover {n : ℕ} (hn : 0 < n) :
    (⋃ k : Fin d → Fin n, realCubeCell n k) = realFinCube d := by
  apply Subset.antisymm
  · exact iUnion_subset (realCubeCell_subset hn)
  · intro x hx
    have hx' : x ∈ Icc (fun _ : Fin d ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) := by
      simpa [realFinCube,show (-1:ℝ)+2=1 by norm_num] using hx
    obtain ⟨k,hk⟩ := corrugationCube_closed_cover (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn x hx'
    exact mem_iUnion.mpr ⟨k,by rwa [realCubeCell_closedBall hn k]⟩

lemma real_closedBall_ae_ball (c : (Fin d → ℝ)) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  rw [ae_eq_set,closedBall_sdiff_ball,sdiff_eq_empty.mpr ball_subset_closedBall,measure_empty]
  exact ⟨Measure.addHaar_sphere volume c r,rfl⟩

lemma realCubeCell_pairwise_aedisjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (AEDisjoint volume on (realCubeCell (d := d) n)) := by
  intro k j hkj
  change AEDisjoint volume (realCubeCell n k) (realCubeCell n j)
  rw [realCubeCell_closedBall hn k,realCubeCell_closedBall hn j]
  exact (corrugationCube_balls_disjoint (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k j hkj).aedisjoint.congr
    (real_closedBall_ae_ball _ _) (real_closedBall_ae_ball _ _)

theorem realCubeCell_integral_sum {n : ℕ} (hn : 0 < n)
    (F : (Fin d → ℝ) → ℝ) (hF : IntegrableOn F (realFinCube d)) :
    (∫ x in realFinCube d, F x) = ∑ k : Fin d → Fin n, ∫ x in realCubeCell n k, F x := by
  have hi : IntegrableOn F (⋃ k : Fin d → Fin n, realCubeCell n k) := by
    rwa [realCubeCell_cover hn]
  have h := integral_iUnion_ae (fun k ↦ (realCubeCell_isCompact n k).measurableSet.nullMeasurableSet)
    (realCubeCell_pairwise_aedisjoint hn) hi
  simpa only [realCubeCell_cover hn,tsum_fintype] using h

omit [NeZero d] in
lemma realCubeCell_mass {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    (volume.restrict (realCubeCell n k)).real univ = (2/(n:ℝ))^d := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  simpa only [realCubeCell,mul_one_div] using
    realScaledCube_mass d (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (div_pos zero_lt_one hnR)

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeCellApproximation.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
def realCubeCellMean (W : (Fin d → ℝ) → ℝ) (n : ℕ) (k : Fin d → Fin n) : ℝ :=
  (∫ x in realCubeCell n k, W x)/(2/(n:ℝ))^d

omit [NeZero d] in
lemma realCubeCell_poincare {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n)
    (W : (Fin d → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realCubeCell n k, ∑ i, (coordPartial W x i)^2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := real_scaledCube_poincare d (corrugationCubeCenter (fun _ ↦ -1) 2 n k)
    (div_pos zero_lt_one hnR) W hW
  simpa only [realCubeCell,realCubeCellMean,mul_one_div,div_pow,one_pow,mul_one_div] using h

theorem realCubeCell_total_error {n : ℕ} (hn : 0 < n)
    (W : (Fin d → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∑ k : Fin d → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube d, ∑ i, (coordPartial W x i)^2) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d → Fin n))) ↦
    realCubeCell_poincare hn k W hW)
  rw [← Finset.mul_sum,← realCubeCell_integral_sum hn] at h
  · exact h
  · exact realFinCube_integrable d _
      (continuous_finsetSum _ (fun i _ ↦ (real_coordPartial_smooth W hW i).continuous.pow 2))

omit [NeZero d] in
lemma realCubeCell_mean_square_le {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n)
    (W : (Fin d → ℝ) → ℝ) (hW : Continuous W) :
    (2/(n:ℝ))^d*(realCubeCellMean W n k)^2 ≤ ∫ x in realCubeCell n k, W x^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_contraction (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
  simpa only [realCubeCell_mass hn,realCubeCellMean] using h

omit [NeZero d] in
lemma realCubeCell_mean_bound {n : ℕ} (hn : 0 < n) (k : Fin d → Fin n)
    (W : (Fin d → ℝ) → ℝ) (hW : Continuous W) {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in realFinCube d, W x^2) ≤ C) :
    |realCubeCellMean W n k| ≤ C/(2/(n:ℝ))^d+1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hm : 0 < (2/(n:ℝ))^d := by positivity
  have hi := setIntegral_mono_set (realFinCube_integrable d _ (hW.pow 2))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (W x)))
    (realCubeCell_subset hn k).eventuallyLE
  have hs := (realCubeCell_mean_square_le hn k W hW).trans (hi.trans hbound)
  have hs' : (realCubeCellMean W n k)^2 ≤ C/(2/(n:ℝ))^d := by
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using hs
  have hv : 0 ≤ C/(2/(n:ℝ))^d := div_nonneg hC hm.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (realCubeCellMean W n k-1),sq_nonneg (realCubeCellMean W n k+1)]

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeCellDistance.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
omit [NeZero d] in
lemma realCubeCellMean_sub (n : ℕ) (k : Fin d → Fin n)
    (W V : (Fin d → ℝ) → ℝ) (hW : Continuous W) (hV : Continuous V) :
    realCubeCellMean (fun x ↦ W x-V x) n k = realCubeCellMean W n k-realCubeCellMean V n k := by
  unfold realCubeCellMean
  rw [integral_sub (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    (hV.continuousOn.integrableOn_compact (realCubeCell_isCompact n k)),sub_div]

theorem realCubeCell_square_decomposition {n : ℕ} (hn : 0 < n)
    (W : (Fin d → ℝ) → ℝ) (hW : Continuous W) :
    (∫ x in realFinCube d, W x^2) =
      (∑ k : Fin d → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2)+
      ∑ k : Fin d → Fin n, (2/(n:ℝ))^d*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_integral_sum hn (fun x ↦ W x^2) (realFinCube_integrable d _ (hW.pow 2)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_decomposition (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k)) 0
  simpa only [sub_zero,realCubeCell_mass hn,realCubeCellMean] using h

theorem realCubeCell_square_bound {n : ℕ} (hn : 0 < n)
    (W : (Fin d → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube d, W x^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube d, ∑ i, (coordPartial W x i)^2)+
      ∑ k : Fin d → Fin n, (2/(n:ℝ))^d*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_square_decomposition hn W hW.continuous]
  exact add_le_add (realCubeCell_total_error hn W hW) le_rfl

omit [NeZero d] in
lemma real_cube_energy_sub (W V : (Fin d → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube d, ∑ i, (coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∫ x in realFinCube d, ∑ i, (coordPartial W x i)^2)+
        (∫ x in realFinCube d, ∑ i, (coordPartial V x i)^2)) := by
  have hp (x : (Fin d → ℝ)) (i : Fin d) :
      coordPartial (fun y ↦ W y-V y) x i = coordPartial W x i-coordPartial V x i := by
    simp only [coordPartial,fderiv_fun_sub (hW.differentiable (by simp) x)
      (hV.differentiable (by simp) x),_root_.sub_apply]
  have hc (F : (Fin d → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
      Continuous (fun x ↦ ∑ i, (coordPartial F x i)^2) :=
    continuous_finsetSum _ (fun i _ ↦ (real_coordPartial_smooth F hF i).continuous.pow 2)
  have hpt (x : (Fin d → ℝ)) : (∑ i, (coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∑ i, (coordPartial W x i)^2)+(∑ i, (coordPartial V x i)^2)) := by
    simp_rw [hp]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (coordPartial W x i+coordPartial V x i)]
  have h := setIntegral_mono_on (μ := volume)
    (realFinCube_integrable d _ (hc _ (hW.sub hV)))
    (realFinCube_integrable d _ (((hc W hW).add (hc V hV)).const_mul 2))
    (realFinCube_isCompact d).measurableSet (fun x _ ↦ hpt x)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,integral_add (realFinCube_integrable d _ (hc W hW))
    (realFinCube_integrable d _ (hc V hV))] at h
  exact h

theorem realCubeCell_distance_bound {n : ℕ} (hn : 0 < n)
    (W V : (Fin d → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube d, (W x-V x)^2) ≤
      (8/(n:ℝ)^2)*((∫ x in realFinCube d, ∑ i, (coordPartial W x i)^2)+
        (∫ x in realFinCube d, ∑ i, (coordPartial V x i)^2))+
      ∑ k : Fin d → Fin n, (2/(n:ℝ))^d*(realCubeCellMean W n k-realCubeCellMean V n k)^2 := by
  have h := realCubeCell_square_bound hn (fun x ↦ W x-V x) (hW.sub hV)
  simp_rw [realCubeCellMean_sub n _ W V hW.continuous hV.continuous] at h
  have he := mul_le_mul_of_nonneg_left (real_cube_energy_sub W V hW hV)
    (show 0 ≤ 4/(n:ℝ)^2 by positivity)
  have ht := h.trans (add_le_add he le_rfl)
  rw [← mul_assoc (4/(n:ℝ)^2) 2,show (4/(n:ℝ)^2)*2=8/(n:ℝ)^2 by ring] at ht
  exact ht

/- Adapted from lean/OAI/Geometry/NodalSets/Elliptic/RealCubeEnergyCompactness.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. -/
theorem real_countable_cube_energy_subsequence {P : Type*} [Countable P]
    (W : P → ℕ → (Fin d → ℝ) → ℝ)
    (hW : ∀ p j, ContDiff ℝ ∞ (W p j)) (C : P → ℝ) (hC : ∀ p, 0 < C p)
    (hbound : ∀ p j, (∫ x in realFinCube d, (W p j x)^2)+
      (∫ x in realFinCube d, ∑ i, (coordPartial (W p j) x i)^2) ≤ C p) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ p, ∀ eps > 0, ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, (∫ x in realFinCube d, (W p (nu i) x-W p (nu j) x)^2) < eps := by
  have hs (p : P) (j : ℕ) : (∫ x in realFinCube d, (W p j x)^2) ≤ C p :=
    (le_add_of_nonneg_right (integral_nonneg (fun x ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)))).trans (hbound p j)
  have he (p : P) (j : ℕ) : (∫ x in realFinCube d, ∑ i, (coordPartial (W p j) x i)^2) ≤ C p :=
    (le_add_of_nonneg_left (integral_nonneg (fun x ↦ sq_nonneg (W p j x)))).trans (hbound p j)
  let localIndex := P × ((n : ℕ) × (Fin d → Fin (n+1)))
  let a : ℕ → localIndex → ℝ := fun j k ↦ realCubeCellMean (W k.1 j) (k.2.1+1) k.2.2
  let B : localIndex → ℝ := fun k ↦ C k.1/(2/((k.2.1+1:ℕ):ℝ))^d+1
  have hb (j : ℕ) (k : localIndex) : |a j k| ≤ B k :=
    realCubeCell_mean_bound (Nat.succ_pos k.2.1) k.2.2 (W k.1 j) (hW k.1 j).continuous (hC k.1).le (hs k.1 j)
  obtain ⟨f,nu,hnu,ht⟩ := real_countable_bounded_subsequence a B hb
  refine ⟨nu,hnu,?_⟩
  intro p eps heps
  obtain ⟨m,hm⟩ := exists_nat_gt (32*C p/eps)
  have hnR : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hn0 : (0:ℝ) < ((m+1:ℕ):ℝ) := zero_lt_one.trans_le hnR
  have hsize : 16*C p/((m+1:ℕ):ℝ)^2 < eps/2 := by
    have hbig : 32*C p/eps < ((m+1:ℕ):ℝ) := hm.trans (by exact_mod_cast Nat.lt_succ_self m)
    have hh := (div_lt_iff₀ heps).mp hbig
    have hsquare : ((m+1:ℕ):ℝ) ≤ ((m+1:ℕ):ℝ)^2 := by nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hn0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare heps.le]
  obtain ⟨N,hN⟩ := real_finite_weighted_cauchy
    (fun (j : ℕ) (k : Fin d → Fin (m+1)) ↦ realCubeCellMean (W p (nu j)) (m+1) k)
    (fun k ↦ f ⟨p,m,k⟩) (fun _ ↦ (2/((m+1:ℕ):ℝ))^d)
    (fun _ ↦ by positivity) (fun k ↦ ht ⟨p,m,k⟩) (eps/2) (by linarith)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have h := realCubeCell_distance_bound (Nat.succ_pos m) (W p (nu i)) (W p (nu j)) (hW p (nu i)) (hW p (nu j))
  have henergy := mul_le_mul_of_nonneg_left (add_le_add (he p (nu i)) (he p (nu j)))
    (show 0 ≤ 8/((m+1:ℕ):ℝ)^2 by positivity)
  have henergy' : (8/((m+1:ℕ):ℝ)^2)*
      ((∫ x in realFinCube d, ∑ k, (coordPartial (W p (nu i)) x k)^2)+
        (∫ x in realFinCube d, ∑ k, (coordPartial (W p (nu j)) x k)^2)) < eps/2 := by
    apply henergy.trans_lt
    calc
      _ = 16*C p/((m+1:ℕ):ℝ)^2 := by ring
      _ < _ := hsize
  exact h.trans_lt (by linarith [henergy',hN i hi j hj])

theorem real_cube_energy_subsequence (W : ℕ → (Fin d → ℝ) → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, (∫ x in realFinCube d, (W j x)^2)+
      (∫ x in realFinCube d, ∑ i, (coordPartial (W j) x i)^2) ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ eps > 0, ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, (∫ x in realFinCube d, (W (nu i) x-W (nu j) x)^2) < eps := by
  obtain ⟨nu,hnu,h⟩ := real_countable_cube_energy_subsequence
    (fun _ : Unit ↦ W) (fun _ ↦ hW) (fun _ ↦ C) (fun _ ↦ hC) (fun _ ↦ hbound)
  exact ⟨nu,hnu,h ()⟩

end
end SlowEquilibration.GenericRellich
