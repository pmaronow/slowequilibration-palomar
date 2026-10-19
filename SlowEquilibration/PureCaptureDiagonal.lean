-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NatLogWindowScales

/-! The diagonal step in source Lemma 9.22. The input is the fixed-deficit
coarse-cover estimate from Proposition 9.16, expressed as a nonnegative
decreasing uncovered mass. No rate for that estimate is assumed. -/

@[expose] public section
namespace SlowEquilibration.PureCaptureDiagonal
noncomputable section
open Filter
open scoped Topology

set_option autoImplicit false

/-- Any monotone family of uncovered masses tending to zero for each fixed
positive deficit admits a vanishing deficit with vanishing uncovered mass.
The cutoff is selected only after all fixed-deficit limits have been given. -/
theorem exists_vanishing_deficit
    (F : ℕ → ℝ → ℝ)
    (hnonneg : ∀ n a, 0 ≤ F n a)
    (hfixed : ∀ a : ℝ, 0 < a → Tendsto (fun n => F n a) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => F n (τ n)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun j => 1 / ((j + 1 : ℕ) : ℝ)
  have ha_pos (j : ℕ) : 0 < a j := by
    dsimp [a]
    positivity
  have hthreshold (j : ℕ) : ∃ N : ℕ, ∀ n ≥ N, F n (a j) < a j := by
    have h := (hfixed (a j) (ha_pos j)).eventually
      (gt_mem_nhds (ha_pos j))
    exact Filter.eventually_atTop.1 h
  let N : ℕ → ℕ := fun j => Classical.choose (hthreshold j)
  have hN (j n : ℕ) (hn : N j ≤ n) : F n (a j) < a j :=
    Classical.choose_spec (hthreshold j) n hn
  let index : ℕ → ℕ := fun n => Nat.findGreatest
    (fun j => j = 0 ∨ N j ≤ n) n
  have hindex : Tendsto index atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    exact Nat.le_findGreatest (by omega : k ≤ n)
      (Or.inr (by omega : N k ≤ n))
  have hindex_pos : ∀ᶠ n : ℕ in atTop, 0 < index n := by
    filter_upwards [eventually_ge_atTop (max 1 (N 1))] with n hn
    exact lt_of_lt_of_le (by omega : 0 < 1)
      (Nat.le_findGreatest (by omega : 1 ≤ n)
        (Or.inr (by omega : N 1 ≤ n)))
  have hchosen : ∀ᶠ n : ℕ in atTop, F n (a (index n)) < a (index n) := by
    filter_upwards [hindex_pos] with n hn
    have hP := Nat.findGreatest_spec (P := fun j => j = 0 ∨ N j ≤ n)
      (m := 0) (n := n) (Nat.zero_le _) (Or.inl rfl)
    exact hN _ _ (hP.resolve_left (Nat.ne_of_gt hn))
  have ha_lim : Tendsto (fun n => a (index n)) atTop (𝓝 0) := by
    simpa only [a, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hindex
  have hF_nonneg : ∀ n, 0 ≤ F n (a (index n)) := fun n => hnonneg n _
  refine ⟨fun n => a (index n), fun n => ha_pos _, ha_lim, ?_⟩
  exact squeeze_zero' (Filter.Eventually.of_forall hF_nonneg)
    (hchosen.mono fun n hn => hn.le) ha_lim

/-- The source diagonal choice, enlarged to include the exact logarithmic
floor. The extra floor changes no limiting cover mass by monotonicity. -/
theorem exists_vanishing_deficit_with_log_floor
    (F : ℕ → ℝ → ℝ)
    (hnonneg : ∀ n a, 0 ≤ F n a)
    (hmono : ∀ n a b, a ≤ b → F n b ≤ F n a)
    (hfixed : ∀ a : ℝ, 0 < a → Tendsto (fun n => F n a) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, (Real.log (n+2 : ℕ))^2/(n+2 : ℕ) ≤ τ n) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => F n (τ n)) atTop (𝓝 0) := by
  obtain ⟨τ₀,hτ₀pos,hτ₀lim,hF₀lim⟩ := exists_vanishing_deficit F hnonneg hfixed
  let floor : ℕ → ℝ := fun n => (Real.log (n+2 : ℕ))^2/(n+2 : ℕ)
  let τ : ℕ → ℝ := fun n => max (τ₀ n) (floor n)
  have hfloorlim : Tendsto floor atTop (𝓝 0) :=
    NatLogWindowScales.log_power_div_dimension_tendsto_zero 2
  have hτlim : Tendsto τ atTop (𝓝 0) := by
    simpa only [τ, max_self] using hτ₀lim.max hfloorlim
  have hFle : ∀ n, F n (τ n) ≤ F n (τ₀ n) := by
    intro n
    exact hmono n _ _ (le_max_left _ _)
  have hFlim : Tendsto (fun n => F n (τ n)) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => hnonneg n _) hFle hF₀lim
  exact ⟨τ, (fun n => lt_of_lt_of_le (hτ₀pos n) (le_max_left _ _)),
    (fun n => le_max_right _ _), hτlim, hFlim⟩

/-- Source centering for physical dimension `n + 2`. -/
def center (e c : ℝ) (n : ℕ) : ℝ :=
  (n+2 : ℕ)*e-Real.log (n+2 : ℕ)/(2*c)

/-- The lower endpoint of the vanishing-deficit critical window is
algebraically exactly the critical-value cutoff of the coarse cover. -/
theorem center_sub_deficit (e c : ℝ) (τ : ℕ → ℝ) (n : ℕ) :
    center e c n-((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) =
      (n+2 : ℕ)*(e-τ n) := by
  unfold center
  ring

/-- The floor is equivalent to the manuscript's explicit ratio bound;
`N = n + 2` ensures the logarithm is strictly positive. -/
theorem log_floor_ratio (τ : ℕ → ℝ) (n : ℕ)
    (hfloor : (Real.log (n+2 : ℕ))^2/(n+2 : ℕ) ≤ τ n) :
    1 ≤ ((n+2 : ℕ)*τ n)/(Real.log (n+2 : ℕ))^2 := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hlog : 0 < Real.log (n+2 : ℕ) := Real.log_pos (by
    exact_mod_cast (show 1 < n+2 by omega))
  have hsq : 0 < (Real.log (n+2 : ℕ))^2 := sq_pos_of_pos hlog
  have heq : (Real.log (n+2 : ℕ))^2 ≤ (n+2 : ℕ)*τ n := by
    calc
      _ = ((Real.log (n+2 : ℕ))^2/(n+2 : ℕ))*(n+2 : ℕ) := by
        field_simp
      _ ≤ τ n*(n+2 : ℕ) := mul_le_mul_of_nonneg_right hfloor hN.le
      _ = _ := mul_comm _ _
  exact (le_div_iff₀ hsq).2 (by simpa only [one_mul] using heq)

/-- The critical-window offset never exceeds the uncentered deficit. -/
theorem deficit_offset_le_uncentered (c : ℝ) (hc : 0 < c) (τ : ℕ → ℝ) (n : ℕ) :
    (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c) ≤ (n+2 : ℕ)*τ n := by
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n+2 by omega))
  have hdiv : 0 ≤ Real.log (n+2 : ℕ)/(2*c) := div_nonneg hlog (by positivity)
  linarith

/-- The physical-window lower offset is eventually positive and sublinear.
The first assertion uses the exact `(log N)^2/N` floor, not a fixed-energy
deficit or an assumed rate for the coarse cover. -/
theorem deficit_offset_positive_and_sublinear
    (c : ℝ) (hc : 0 < c) (τ : ℕ → ℝ)
    (hfloor : ∀ n, (Real.log (n+2 : ℕ))^2/(n+2 : ℕ) ≤ τ n)
    (hτlim : Tendsto τ atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop,
      0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
    Tendsto
      (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
      atTop (𝓝 (0 : ℝ)) := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hloglarge : ∀ᶠ n : ℕ in atTop,
      1/(2*c) < Real.log (n+2 : ℕ) :=
    hloglim.eventually_gt_atTop (1/(2*c))
  have hapos : ∀ᶠ n : ℕ in atTop,
      0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c) := by
    filter_upwards [hloglarge] with n hn
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hlog : 0 < Real.log (n+2 : ℕ) := by
      have : 0 < 1/(2*c) := by positivity
      linarith
    have hsq : (Real.log (n+2 : ℕ))^2 ≤ (n+2 : ℕ)*τ n := by
      calc
        _ = ((Real.log (n+2 : ℕ))^2/(n+2 : ℕ))*(n+2 : ℕ) := by
          field_simp
        _ ≤ τ n*(n+2 : ℕ) := mul_le_mul_of_nonneg_right (hfloor n) hN.le
        _ = _ := mul_comm _ _
    have hsplit : Real.log (n+2 : ℕ)/(2*c) =
        Real.log (n+2 : ℕ)*(1/(2*c)) := by ring
    rw [hsplit]
    nlinarith [mul_pos hlog (sub_pos.mpr hn)]
  have hlogdiv : Tendsto
      (fun n : ℕ => Real.log (n+2 : ℕ)/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one] using
      NatLogWindowScales.log_power_div_dimension_tendsto_zero 1
  have hsub : Tendsto (fun n : ℕ =>
      τ n-(1/(2*c))*(Real.log (n+2 : ℕ)/(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      hτlim.sub (hlogdiv.const_mul (1/(2*c)))
  refine ⟨hapos,?_⟩
  convert hsub using 1
  · funext n
    have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp

/-- Combined analytic content of the diagonal construction in source 9.22.
`F n τ` is the expected uncovered Gibbs mass for the physical dimension
`N = n + 2`; its two input properties are precisely positivity,
monotonicity and source Proposition 9.16 at each fixed deficit. -/
theorem source_pc_diagonal_core
    (F : ℕ → ℝ → ℝ) (e c : ℝ) (hc : 0 < c)
    (hnonneg : ∀ n a, 0 ≤ F n a)
    (hmono : ∀ n a b, a ≤ b → F n b ≤ F n a)
    (hcoarse : ∀ a : ℝ, 0 < a → Tendsto (fun n => F n a) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, (Real.log (n+2 : ℕ))^2/(n+2 : ℕ) ≤ τ n) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => F n (τ n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
      Tendsto
        (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) ∧
      ∀ n, center e c n-((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) =
        (n+2 : ℕ)*(e-τ n) := by
  obtain ⟨τ,hτpos,hfloor,hτlim,hFlim⟩ :=
    exists_vanishing_deficit_with_log_floor F hnonneg hmono hcoarse
  obtain ⟨hapos,hasub⟩ :=
    deficit_offset_positive_and_sublinear c hc τ hfloor hτlim
  exact ⟨τ,hτpos,hfloor,hτlim,hFlim,hapos,hasub,center_sub_deficit e c τ⟩

end
end SlowEquilibration.PureCaptureDiagonal
