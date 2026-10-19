-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicirclePotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Uniform actual Jacobi/Hermite determinant prefactors

The proved finite Riccati equation and actual logarithmic infinity anchor yield
bounded prefactors for the literal Jacobi characteristic polynomial. Identifying
this polynomial with the signed GOE determinant expectation is a separate step.
-/

namespace SlowEquilibration.JacobiPrefactors

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter Polynomial
open OAI.CriticalSK GOELogPotential JacobiLogLimit
open scoped Topology BigOperators

lemma normalized_resolvent_eq_empirical (n : ℕ) (s : ℝ) :
    jacobiNormalizedResolvent n s = OAI.CriticalSK.empiricalResolvent (jacobiGaps (n + 1)) s := by
  unfold jacobiNormalizedResolvent OAI.CriticalSK.empiricalResolvent
  change (∑ i, (fun x : ℝ => (s + x)⁻¹) (orderedJacobiGaps n i)) / (n + 1 : ℝ) = _
  rw [sum_orderedJacobiGaps n (fun x : ℝ => (s + x)⁻¹)]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]

lemma empirical_square_le_inv_sq (n : ℕ) {s : ℝ} (hs : 0 < s) :
    empiricalResolventSquare (jacobiGaps (n + 1)) s ≤ 1 / s ^ 2 := by
  have hpoint (i : Fin (n + 1)) : (s + jacobiGaps (n + 1) i)⁻¹ ^ 2 ≤ s⁻¹ ^ 2 := by
    have hg := jacobiGaps_nonneg (n + 1) i
    have hip : 0 < s + jacobiGaps (n + 1) i := by linarith
    have hi := (inv_le_inv₀ hip hs).mpr (by linarith : s ≤ s + jacobiGaps (n + 1) i)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hip.le) hi 2
  unfold empiricalResolventSquare
  calc
    _ ≤ (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ * ∑ _i : Fin (n + 1), s⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm : (n + 1 : ℝ) ≠ 0 := by positivity
      simp only [Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ hm, one_mul, inv_pow, one_div]

/-- A true finite-dimensional error bound, requiring no large-dimension scale. -/
lemma normalized_resolvent_error_bound (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ semicircleResolvent s - jacobiNormalizedResolvent n s ∧
      (n + 1 : ℝ) * (semicircleResolvent s - jacobiNormalizedResolvent n s) ≤ 1 / s ^ 3 := by
  have hR : ∀ u : ℝ, 0 < u →
      (OAI.CriticalSK.empiricalResolvent (jacobiGaps (n + 1)) u) ^ 2 -
        (2 + u) * OAI.CriticalSK.empiricalResolvent (jacobiGaps (n + 1)) u + 1 =
        empiricalResolventSquare (jacobiGaps (n + 1)) u / Fintype.card (Fin (n + 1)) := by
    intro u hu
    simpa only [Fintype.card_fin, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using jacobi_riccati (Nat.succ_pos n) hu
  have hd := empiricalResolvent_root_difference _ (jacobiGaps_nonneg (n + 1)) hR hs
  rw [← normalized_resolvent_eq_empirical] at hd
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hd
  refine ⟨hd.1, ?_⟩
  have hm : 0 < (n + 1 : ℝ) := by positivity
  have hroot : 0 < Real.sqrt (s * (4 + s)) := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hrootle : s ≤ Real.sqrt (s * (4 + s)) := by
    apply (Real.le_sqrt hs.le (semicircle_discriminant_pos hs).le).mpr
    nlinarith
  have hmul := (mul_le_mul_of_nonneg_left hd.2 hm.le)
  calc
    _ ≤ empiricalResolventSquare (jacobiGaps (n + 1)) s / Real.sqrt (s * (4 + s)) := by
      convert hmul using 1
      field_simp
    _ ≤ (1 / s ^ 2) / Real.sqrt (s * (4 + s)) :=
      div_le_div_of_nonneg_right (empirical_square_le_inv_sq n hs) hroot.le
    _ ≤ (1 / s ^ 2) / s :=
      div_le_div_of_nonneg_left (by positivity) hs hrootle
    _ = _ := by field_simp

def logExcess (n : ℕ) (s : ℝ) : ℝ :=
  (n + 1 : ℝ) * (jacobiNormalizedLog n s - outsideSpectralPotential s)

lemma logExcess_hasDerivAt (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (logExcess n)
      ((n + 1 : ℝ) * (jacobiNormalizedResolvent n s - semicircleResolvent s)) s := by
  exact ((jacobiNormalizedLog_hasDerivAt n hs).sub
    (outsideSpectralPotential_hasDerivAt hs)).const_mul _

lemma jacobi_log_minus_log_tendsto (n : ℕ) :
    Tendsto (fun s : ℝ => jacobiNormalizedLog n s - Real.log (2 + s)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ s : ℝ in atTop, 0 ≤ |jacobiNormalizedLog n s - Real.log (2 + s)| ∧
      |jacobiNormalizedLog n s - Real.log (2 + s)| ≤ 2 / s := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact ⟨abs_nonneg _, jacobi_log_anchor_bound n (by linarith)⟩
  have ht := squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
    (tendsto_id.const_div_atTop 2)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

lemma logExcess_tendsto_zero (n : ℕ) : Tendsto (logExcess n) atTop (𝓝 0) := by
  have h := ((jacobi_log_minus_log_tendsto n).sub outsideSpectralPotential_minus_log_tendsto).const_mul
    (n + 1 : ℝ)
  convert h using 1
  · funext s; dsimp [logExcess]; ring
  · simp

lemma halfInvSquare_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ => 1 / (2 * u ^ 2)) (-1 / s ^ 3) s := by
  have h := (((hasDerivAt_id s).pow 2).const_mul 2).inv (by positivity : 2 * s ^ 2 ≠ 0)
  convert h using 1
  · funext u
    change 1 / (2 * u ^ 2) = (2 * u ^ 2)⁻¹
    exact one_div _
  · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp

/-- The signed Jacobi/Hermite log determinant differs from its actual density
potential by a nonnegative, dimension-uniform bounded amount. -/
theorem logExcess_bounds (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ logExcess n s ∧ logExcess n s ≤ 1 / (2 * s ^ 2) := by
  have hc : ContinuousOn (logExcess n) (Ioi (0 : ℝ)) :=
    fun u hu => (logExcess_hasDerivAt n hu).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (logExcess n) (Ioi (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _) hc
    · intro u hu
      rw [interior_Ioi] at hu
      exact (logExcess_hasDerivAt n hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      rw [(logExcess_hasDerivAt n hu).deriv]
      have h := (normalized_resolvent_error_bound n hu).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hlower : 0 ≤ logExcess n s := by
    apply le_of_tendsto (logExcess_tendsto_zero n)
    filter_upwards [eventually_ge_atTop s] with u hu
    exact hanti hs (hs.trans_le hu) hu
  let f : ℝ → ℝ := fun u => logExcess n u - 1 / (2 * u ^ 2)
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt f
      ((n + 1 : ℝ) * (jacobiNormalizedResolvent n u - semicircleResolvent u) + 1 / u ^ 3) u := by
    intro u hu
    have h := (logExcess_hasDerivAt n hu).sub (halfInvSquare_hasDerivAt hu)
    convert h using 1
    ring
  have hfmono : MonotoneOn f (Ioi (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      exact (hd u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      rw [(hd u hu).deriv]
      have h := (normalized_resolvent_error_bound n hu).2
      linarith
  have hden : Tendsto (fun u : ℝ => 2 * u ^ 2) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hflim : Tendsto f atTop (𝓝 0) := by
    have h := (logExcess_tendsto_zero n).sub (hden.const_div_atTop 1)
    simpa only [sub_zero] using h
  have hupper : f s ≤ 0 := by
    apply ge_of_tendsto hflim
    filter_upwards [eventually_ge_atTop s] with u hu
    exact hfmono hs (hs.trans_le hu) hu
  exact ⟨hlower, by dsimp [f] at hupper; linarith⟩

/-- The actual finite scaled-Hermite polynomial value, with GOE normalization. -/
def hermiteValue (n : ℕ) (z : ℝ) : ℝ :=
  (scaledHermite (n + 1 : ℝ)⁻¹ (n + 1)).eval z

lemma hermiteValue_eq_gap_product (n : ℕ) (s : ℝ) :
    hermiteValue n (2 + s) = ∏ i : Fin (n + 1), (s + jacobiGaps (n + 1) i) := by
  unfold hermiteValue
  rw [← jacobi_charpoly (a := (n + 1 : ℝ)⁻¹) (by positivity) (n + 1),
    (jacobi_hermitian (n + 1 : ℝ)⁻¹ (n + 1)).charpoly_eq, eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id_eq, jacobiGaps, Nat.cast_add, Nat.cast_one]
  ring

lemma hermiteValue_pos (n : ℕ) {s : ℝ} (hs : 0 < s) : 0 < hermiteValue n (2 + s) := by
  rw [hermiteValue_eq_gap_product]
  exact Finset.prod_pos (fun i _ => add_pos_of_pos_of_nonneg hs (jacobiGaps_nonneg _ _))

lemma log_hermiteValue (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Real.log (hermiteValue n (2 + s)) = (n + 1 : ℝ) * jacobiNormalizedLog n s := by
  rw [hermiteValue_eq_gap_product,
    Real.log_prod (fun i _ => (add_pos_of_pos_of_nonneg hs (jacobiGaps_nonneg _ i)).ne')]
  unfold jacobiNormalizedLog
  have hsum := sum_orderedJacobiGaps n (fun g : ℝ => Real.log (s + g))
  rw [hsum]
  field_simp

/-- Actual scaled-Hermite logarithmic prefactors above the positive edge. -/
theorem log_hermiteValue_potential_bounds (n : ℕ) {z : ℝ} (hz : 2 < z) :
    0 ≤ Real.log (hermiteValue n z) - (n + 1 : ℝ) * SemicirclePotential.potential z ∧
      Real.log (hermiteValue n z) - (n + 1 : ℝ) * SemicirclePotential.potential z ≤
        1 / (2 * (z - 2) ^ 2) := by
  have hs : 0 < z - 2 := by linarith
  have h := logExcess_bounds n hs
  have heq : logExcess n (z - 2) =
      Real.log (hermiteValue n z) - (n + 1 : ℝ) * SemicirclePotential.potential z := by
    have hlog := log_hermiteValue n hs
    rw [show 2 + (z - 2) = z by ring] at hlog
    rw [SemicirclePotential.potential_eq_outsideSpectralPotential hz, hlog]
    dsimp [logExcess]
    ring
  rw [heq] at h
  exact h

/-- Literal polynomial bounded prefactors, for every positive dimension.
The lower constant is exactly one, as in the source. -/
theorem hermiteValue_prefactors (n : ℕ) {z : ℝ} (hz : 2 < z) :
    Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential z) ≤ hermiteValue n z ∧
      hermiteValue n z ≤ Real.exp (1 / (2 * (z - 2) ^ 2)) *
        Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential z) := by
  have hs : 0 < z - 2 := by linarith
  have hp : 0 < hermiteValue n z := by
    convert hermiteValue_pos n hs using 1
    congr 1
    ring
  have h := log_hermiteValue_potential_bounds n hz
  constructor
  · calc
      _ ≤ Real.exp (Real.log (hermiteValue n z)) := Real.exp_le_exp.mpr (by linarith [h.1])
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (hermiteValue n z)) := (Real.exp_log hp).symm
      _ ≤ Real.exp (1 / (2 * (z - 2) ^ 2) + (n + 1 : ℝ) * SemicirclePotential.potential z) :=
        Real.exp_le_exp.mpr (by linarith [h.2])
      _ = _ := Real.exp_add _ _

/-- The polynomial prefactor is uniform over every real shift above a fixed
positive edge gap, including all positive dimensions. -/
theorem hermiteValue_prefactors_uniform (n : ℕ) {d z : ℝ} (hd : 0 < d)
    (hz : 2 + d ≤ z) :
    Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential z) ≤ hermiteValue n z ∧
      hermiteValue n z ≤ Real.exp (1 / (2 * d ^ 2)) *
        Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential z) := by
  have hz2 : 2 < z := by linarith
  have h := hermiteValue_prefactors n hz2
  refine ⟨h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 < 2 * d ^ 2)
  nlinarith

end
end SlowEquilibration.JacobiPrefactors
