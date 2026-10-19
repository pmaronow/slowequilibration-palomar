-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SmoothSwitch
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Measure.Real

/-! A finite family of genuine smooth negative-overlap cutoffs, with
pairwise disjoint transition shells. Ordinary probability mass bounds
select one cutoff in L¹; genuine Weierstrass approximation supplies
polynomial GG tests selected before the probability law or dimension. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGCutoffs

open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators

set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Width of each of M disjoint shells between -ε and -ε/2. -/
def width (ε : ℝ) (M : ℕ) : ℝ := ε/(2*(M:ℝ))
def leftEndpoint (ε : ℝ) (M : ℕ) (j : Fin M) : ℝ := -ε+(j:ℝ)*width ε M
def rightEndpoint (ε : ℝ) (M : ℕ) (j : Fin M) : ℝ := -ε+((j:ℕ)+1:ℕ)*width ε M
def shell (ε : ℝ) (M : ℕ) (j : Fin M) : Set ℝ :=
  Ioo (leftEndpoint ε M j) (rightEndpoint ε M j)

/-- A literal C∞ decreasing switch, not a supplied indicator approximation. -/
def cutoff (ε : ℝ) (M : ℕ) (j : Fin M) (r : ℝ) : ℝ :=
  1-SmoothSwitch.switch ((r-leftEndpoint ε M j)/width ε M)

theorem width_pos {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) : 0 < width ε M := by
  unfold width
  positivity

theorem cutoff_contDiff (ε : ℝ) (M : ℕ) (j : Fin M) : ContDiff ℝ ∞ (cutoff ε M j) := by
  exact contDiff_const.sub (SmoothSwitch.contDiff_switch.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem cutoff_mem (ε : ℝ) (M : ℕ) (j : Fin M) (r : ℝ) :
    cutoff ε M j r∈Icc (0:ℝ) 1 := by
  have h0 := SmoothSwitch.nonneg ((r-leftEndpoint ε M j)/width ε M)
  have h1 := SmoothSwitch.le_one ((r-leftEndpoint ε M j)/width ε M)
  unfold cutoff
  constructor <;> linarith

theorem right_eq_left_add_width (ε : ℝ) (M : ℕ) (j : Fin M) :
    rightEndpoint ε M j=leftEndpoint ε M j+width ε M := by
  unfold rightEndpoint leftEndpoint
  simp only [Nat.cast_add,Nat.cast_one]
  ring

theorem cutoff_one_of_le_left {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) {r : ℝ} (hr : r ≤ leftEndpoint ε M j) : cutoff ε M j r=1 := by
  unfold cutoff
  rw [SmoothSwitch.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hr) (width_pos hε hM).le), sub_zero]

theorem cutoff_zero_of_right_le {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) {r : ℝ} (hr : rightEndpoint ε M j ≤ r) : cutoff ε M j r=0 := by
  unfold cutoff
  rw [SmoothSwitch.one_of_one_le ((le_div_iff₀ (width_pos hε hM)).mpr (by
    rw [right_eq_left_add_width] at hr
    simp only [one_mul]
    linarith)), sub_self]

theorem endpoints_in_negative_band {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) : -ε ≤ leftEndpoint ε M j ∧ rightEndpoint ε M j ≤ -ε/2 := by
  have hw := width_pos hε hM
  have hj : ((j:ℕ)+1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hprod := mul_le_mul_of_nonneg_right hj hw.le
  have hMw : (M:ℝ)*width ε M=ε/2 := by
    unfold width
    have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp
  rw [hMw] at hprod
  unfold leftEndpoint rightEndpoint
  constructor
  · have hp : 0 ≤ (j:ℝ)*width ε M := mul_nonneg (Nat.cast_nonneg _) hw.le
    linarith
  · norm_cast at hprod ⊢
    linarith

theorem cutoff_one_on_negative {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) {r : ℝ} (hr : r ≤ -ε) : cutoff ε M j r=1 :=
  cutoff_one_of_le_left hε hM j (hr.trans (endpoints_in_negative_band hε hM j).1)

theorem cutoff_zero_above_half {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) {r : ℝ} (hr : -ε/2 ≤ r) : cutoff ε M j r=0 :=
  cutoff_zero_of_right_le hε hM j ((endpoints_in_negative_band hε hM j).2.trans hr)

/-- The finite transition intervals are genuinely pairwise disjoint. -/
theorem shells_disjoint {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    {i j : Fin M} (hij : i ≠ j) : Disjoint (shell ε M i) (shell ε M j) := by
  have hw := width_pos hε hM
  have hordered {i j : Fin M} (hij : i<j) : rightEndpoint ε M i ≤ leftEndpoint ε M j := by
    have hv : ((i:ℕ)+1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hp := mul_le_mul_of_nonneg_right hv hw.le
    unfold rightEndpoint leftEndpoint
    simp only [Nat.cast_add,Nat.cast_one]
    exact add_le_add (le_refl (-ε)) hp
  rcases lt_or_gt_of_ne hij with hij | hji
  · apply Set.disjoint_left.mpr
    intro r hi hj
    have hh := hordered hij
    change r∈Ioo _ _ at hi hj
    linarith [hi.2,hj.1]
  · apply Disjoint.symm
    apply Set.disjoint_left.mpr
    intro r hj hi
    have hh := hordered hji
    change r∈Ioo _ _ at hi hj
    linarith [hj.2,hi.1]

/-- The failure of a cutoff to be an indicator is supported on its own
shell, so the total family of such failures has small averaged mass. -/
theorem cutoff_defect_le_shell {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) (r : ℝ) :
    cutoff ε M j r*(1-cutoff ε M j r) ≤ (shell ε M j).indicator (fun _ => (1:ℝ)) r := by
  have hmem := cutoff_mem ε M j r
  by_cases hr : r∈shell ε M j
  · rw [indicator_of_mem hr]
    nlinarith [hmem.1,hmem.2]
  · rw [indicator_of_notMem hr]
    have hnot : ¬(leftEndpoint ε M j<r ∧ r<rightEndpoint ε M j) := hr
    by_cases hl : r ≤ leftEndpoint ε M j
    · rw [cutoff_one_of_le_left hε hM j hl]
      norm_num
    · have hb : rightEndpoint ε M j ≤ r := by push Not at hnot; exact hnot (lt_of_not_ge hl)
      rw [cutoff_zero_of_right_le hε hM j hb]
      norm_num

/-- Actual probability masses of the fixed disjoint shells sum to at most one. -/
theorem shell_mass_sum_le_one (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) :
    (∑ j : Fin M, ρ.real (shell ε M j)) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := ρ) (s := Finset.univ)
    (fun j _ => measurableSet_Ioo) (fun i hi j hj hij => shells_disjoint hε hM hij)
  rwa [probReal_univ] at h

/-- One of the predetermined finite cutoffs has actual shell mass at most 1/M. -/
theorem exists_shell_mass_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) :
    ∃ j : Fin M, ρ.real (shell ε M j) ≤ 1/(M:ℝ) := by
  classical
  let _ : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  by_contra h
  push Not at h
  have hs : (∑ _j : Fin M, 1/(M:ℝ)) < ∑ j : Fin M, ρ.real (shell ε M j) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h j)
  have heq : (∑ _j : Fin M, 1/(M:ℝ))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp
  rw [heq] at hs
  linarith [shell_mass_sum_le_one ρ hε hM]

/-- Actual Weierstrass approximation of every member of the fixed family.
The polynomials are selected before any disorder dimension or base law. -/
theorem exists_polynomial_family (ε : ℝ) (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Fin M → Polynomial ℝ, ∀ j r, r∈Icc (-1:ℝ) 1 →
      |(P j).eval r-cutoff ε M j r| < δ := by
  have hp (j : Fin M) := exists_polynomial_near_of_continuousOn (-1) 1
    (cutoff ε M j) (cutoff_contDiff ε M j).continuous.continuousOn δ hδ
  choose P hP using hp
  exact ⟨P,fun j r hr => hP j r hr⟩

/-- Pointwise L¹ difference from the associated negative step is
supported precisely on the corresponding predetermined shell. -/
theorem cutoff_indicator_difference_le_shell {ε : ℝ} {M : ℕ}
    (hε : 0 < ε) (hM : 0 < M) (j : Fin M) (r : ℝ) :
    |cutoff ε M j r-(Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ)) r| ≤
      (shell ε M j).indicator (fun _ => (1:ℝ)) r := by
  have hm := cutoff_mem ε M j r
  by_cases hr : r∈shell ε M j
  · rw [indicator_of_mem hr]
    have hl : r∉Iic (leftEndpoint ε M j) := not_le.mpr hr.1
    rw [indicator_of_notMem hl,sub_zero,abs_of_nonneg hm.1]
    exact hm.2
  · rw [indicator_of_notMem hr]
    by_cases hl : r ≤ leftEndpoint ε M j
    · rw [cutoff_one_of_le_left hε hM j hl,indicator_of_mem (show r ∈ Iic (leftEndpoint ε M j) from hl),sub_self,abs_zero]
    · have hb : rightEndpoint ε M j ≤ r :=
        not_lt.mp (fun h => hr ⟨lt_of_not_ge hl,h⟩)
      rw [cutoff_zero_of_right_le hε hM j hb,indicator_of_notMem (show r ∉ Iic (leftEndpoint ε M j) from hl),sub_self,abs_zero]

/-- Actual cutoff-indicator L¹ distance under the ordinary overlap law. -/
theorem cutoff_indicator_L1_le_shell_mass (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) (j : Fin M) :
    (∫ r, |cutoff ε M j r-(Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ)) r| ∂ρ) ≤
      ρ.real (shell ε M j) := by
  have hψ : Integrable (cutoff ε M j) ρ := by
    apply Integrable.of_bound (cutoff_contDiff ε M j).continuous.measurable.aestronglyMeasurable 1
    exact .of_forall fun r => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_mem ε M j r).1]
      exact (cutoff_mem ε M j r).2
  have hstep : Integrable ((Iic (leftEndpoint ε M j)).indicator (fun _ : ℝ => (1:ℝ))) ρ :=
    (integrable_const (μ := ρ) (1:ℝ)).indicator measurableSet_Iic
  have hI := (integrable_const (μ := ρ) (1:ℝ)).indicator (show MeasurableSet (shell ε M j) from measurableSet_Ioo)
  have h := integral_mono_ae (hψ.sub hstep).abs hI
    (.of_forall (cutoff_indicator_difference_le_shell hε hM j))
  rw [integral_indicator_const 1 (show MeasurableSet (shell ε M j) from measurableSet_Ioo),
    smul_eq_mul,mul_one] at h
  exact h

/-- The true idempotence error of the cutoff is bounded by actual shell mass. -/
theorem cutoff_defect_integral_le_shell_mass (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) (j : Fin M) :
    (∫ r, cutoff ε M j r*(1-cutoff ε M j r) ∂ρ) ≤ ρ.real (shell ε M j) := by
  have hψ := (cutoff_contDiff ε M j).continuous
  have hi : Integrable (fun r => cutoff ε M j r*(1-cutoff ε M j r)) ρ := by
    apply Integrable.of_bound (hψ.mul (continuous_const.sub hψ)).measurable.aestronglyMeasurable 1
    exact .of_forall fun r => by
      have hm := cutoff_mem ε M j r
      rw [Real.norm_eq_abs]
      change |cutoff ε M j r*(1-cutoff ε M j r)| ≤ 1
      rw [abs_of_nonneg (mul_nonneg hm.1 (sub_nonneg.mpr hm.2))]
      nlinarith [hm.1,hm.2]
  have hI := (integrable_const (μ := ρ) (1:ℝ)).indicator (show MeasurableSet (shell ε M j) from measurableSet_Ioo)
  have h := integral_mono_ae hi hI (.of_forall (cutoff_defect_le_shell hε hM j))
  rw [integral_indicator_const 1 (show MeasurableSet (shell ε M j) from measurableSet_Ioo),
    smul_eq_mul,mul_one] at h
  exact h

/-- A single index in the fixed finite family controls both actual
indicator approximation and the cutoff's idempotence defect by 1/M. -/
theorem exists_cutoff_L1_and_defect_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) :
    ∃ j : Fin M,
      (∫ r, |cutoff ε M j r-(Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ)) r| ∂ρ) ≤ 1/(M:ℝ) ∧
      (∫ r, cutoff ε M j r*(1-cutoff ε M j r) ∂ρ) ≤ 1/(M:ℝ) := by
  obtain ⟨j,hj⟩ := exists_shell_mass_le ρ hε hM
  exact ⟨j,(cutoff_indicator_L1_le_shell_mass ρ hε hM j).trans hj,
    (cutoff_defect_integral_le_shell_mass ρ hε hM j).trans hj⟩

/-- Every predetermined cutoff dominates the original negative event. -/
theorem negative_indicator_le_cutoff {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) (r : ℝ) :
    (Iic (-ε)).indicator (fun _ => (1:ℝ)) r ≤ cutoff ε M j r := by
  by_cases hr : r≤-ε
  · rw [indicator_of_mem (show r∈Iic (-ε) from hr),cutoff_one_on_negative hε hM j hr]
  · rw [indicator_of_notMem (show r∉Iic (-ε) from hr)]
    exact (cutoff_mem ε M j r).1

/-- Soft stars lie below genuine negative stars with threshold ε/2. -/
theorem cutoff_le_half_negative_indicator {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M)
    (j : Fin M) (r : ℝ) :
    cutoff ε M j r ≤ (Iic (-ε/2)).indicator (fun _ => (1:ℝ)) r := by
  by_cases hr : r≤-ε/2
  · rw [indicator_of_mem (show r∈Iic (-ε/2) from hr)]
    exact (cutoff_mem ε M j r).2
  · rw [indicator_of_notMem (show r∉Iic (-ε/2) from hr),
      cutoff_zero_above_half hε hM j (le_of_lt (lt_of_not_ge hr))]

/-- Degree and coefficient bounds of the whole predetermined polynomial
family are finite constants chosen before the base probability law. -/
theorem exists_bounded_polynomial_family (ε : ℝ) (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Fin M → Polynomial ℝ, ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      (∀ j r, r∈Icc (-1:ℝ) 1 → |(P j).eval r-cutoff ε M j r| < δ) ∧
      (∀ j, (P j).natDegree ≤ K) ∧
      (∀ j, (∑ k ∈ Finset.range (K+1), |(P j).coeff k|) ≤ C) := by
  classical
  obtain ⟨P,hP⟩ := exists_polynomial_family ε M hδ
  let K : ℕ := Finset.univ.sup (fun j : Fin M => (P j).natDegree)
  let C : ℝ := 1+∑ j : Fin M, ∑ k ∈ Finset.range (K+1), |(P j).coeff k|
  have hc : 0 < C := by
    have hs : 0 ≤ ∑ j : Fin M, ∑ k ∈ Finset.range (K+1), |(P j).coeff k| :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
    dsimp [C]
    linarith
  refine ⟨P,K,C,hc,hP,?_,?_⟩
  · intro j
    exact Finset.le_sup (f := fun j : Fin M => (P j).natDegree) (Finset.mem_univ j)
  · intro j
    have hs := Finset.single_le_sum
      (f := fun j : Fin M => ∑ k ∈ Finset.range (K+1), |(P j).coeff k|)
      (fun j _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ j)
    dsimp [C]
    linarith

end SlowEquilibration.GaussianGGCutoffs
