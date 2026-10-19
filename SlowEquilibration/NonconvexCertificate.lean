-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LogEnclosure
public import SlowEquilibration.DoubleWellPositive
public import SlowEquilibration.InverseSqrtCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.Positivity

/-!
# The scalar strict one-step certificate for the degree 4 / degree 12 example

All parameters are the manuscript's actual logarithmic parameters. The
first-variation function is defined by its interval integral, rather than by
assuming the contact equations or its sign.
-/

@[expose] public section

namespace SlowEquilibration.NonconvexCertificate

open MeasureTheory Set Filter
open Certificate LogEnclosure

noncomputable section

abbrev t : ℝ := exampleParameter

def Q : ℝ := 9 / 10
def x : ℝ := 5 / 9
def C : ℝ := 3 / 5
def b : ℝ := t * (10 / 9 : ℝ) ^ 8
def betaSq : ℝ := 15 / (Q ^ 3 * (4 + 12 * t))
def beta : ℝ := Real.sqrt betaSq

def xi (r : ℝ) : ℝ := r ^ 4 + b * r ^ 12
def xi1 (r : ℝ) : ℝ := 4 * r ^ 3 + 12 * b * r ^ 11
def xi2 (r : ℝ) : ℝ := 12 * r ^ 2 + 132 * b * r ^ 10
def xi3 (r : ℝ) : ℝ := 24 * r + 1320 * b * r ^ 9
def xi4 (r : ℝ) : ℝ := 24 + 11880 * b * r ^ 8

lemma t_pos : 0 < t := by
  have h := exampleParameter_enclosure.1
  norm_num [tMinus] at h
  linarith

lemma four_add_t_pos : 0 < 4 + 12 * t := by linarith [t_pos]
lemma Q_pos : 0 < Q := by norm_num [Q]
lemma Q_lt_one : Q < 1 := by norm_num [Q]
lemma x_pos : 0 < x := by norm_num [x]
lemma b_pos : 0 < b := by
  unfold b
  exact mul_pos t_pos (by positivity)
lemma betaSq_pos : 0 < betaSq := by
  unfold betaSq
  exact div_pos (by norm_num) (mul_pos (pow_pos Q_pos _) four_add_t_pos)
lemma beta_pos : 0 < beta := Real.sqrt_pos.2 betaSq_pos
lemma beta_sq : beta ^ 2 = betaSq := Real.sq_sqrt betaSq_pos.le

lemma xi_hasDerivAt (r : ℝ) : HasDerivAt xi (xi1 r) r := by
  have h := ((hasDerivAt_id r).pow 4).add (((hasDerivAt_id r).pow 12).const_mul b)
  convert h using 1 <;> try funext z
  all_goals norm_num [xi, xi1] <;> ring

lemma xi1_hasDerivAt (r : ℝ) : HasDerivAt xi1 (xi2 r) r := by
  have h := (((hasDerivAt_id r).pow 3).const_mul 4).add
    (((hasDerivAt_id r).pow 11).const_mul (12 * b))
  convert h using 1 <;> try funext z
  all_goals norm_num [xi1, xi2] <;> ring

lemma xi2_hasDerivAt (r : ℝ) : HasDerivAt xi2 (xi3 r) r := by
  have h := (((hasDerivAt_id r).pow 2).const_mul 12).add
    (((hasDerivAt_id r).pow 10).const_mul (132 * b))
  convert h using 1 <;> try funext z
  all_goals norm_num [xi2, xi3] <;> ring

lemma xi3_hasDerivAt (r : ℝ) : HasDerivAt xi3 (xi4 r) r := by
  have h := ((hasDerivAt_id r).const_mul 24).add
    (((hasDerivAt_id r).pow 9).const_mul (1320 * b))
  convert h using 1 <;> try funext z
  all_goals norm_num [xi3, xi4] <;> ring

lemma parameter_identity : (1 + t) / (4 + 12 * t) = (6 * Real.log 6 - 5) / 25 := by
  have hrel : t * (72 * Real.log 6 - 85) = 45 - 24 * Real.log 6 := by
    unfold t exampleParameter
    exact div_mul_cancel₀ _ exampleParameter_denominator_pos.ne'
  apply (div_eq_iff four_add_t_pos.ne').2
  nlinarith [hrel]

lemma b_Q_pow : b * Q ^ 8 = t := by norm_num [b, Q]; ring

lemma xi_at_Q : xi Q = Q ^ 4 * (1 + t) := by norm_num [xi, b, Q]; ring
lemma xi1_at_Q : xi1 Q = Q ^ 3 * (4 + 12 * t) := by norm_num [xi1, b, Q]; ring
lemma xi2_at_Q : xi2 Q = Q ^ 2 * (12 + 132 * t) := by norm_num [xi2, b, Q]; ring

lemma contact_slope_equation : betaSq * xi1 Q = 15 := by
  rw [xi1_at_Q]
  unfold betaSq
  field_simp [Q_pos.ne', four_add_t_pos.ne']

lemma contact_value_equation : x ^ 2 * betaSq * xi Q = Real.log 6 - 5 / 6 := by
  rw [xi_at_Q]
  have h : x ^ 2 * betaSq * (Q ^ 4 * (1 + t)) =
      (25 / 6 : ℝ) * ((1 + t) / (4 + 12 * t)) := by
    dsimp [x, betaSq, Q]
    field_simp [four_add_t_pos.ne']
    ring
  rw [h, parameter_identity]
  ring

/-- The scaled first variation below the contact, as in (5.43). -/
def U (r : ℝ) : ℝ :=
  -Real.log (1 - 5 * r / 6) - 5 * r / 6 -
    25 / (6 * (4 + 12 * t)) * (r ^ 4 + t * r ^ 12)

def U1 (r : ℝ) : ℝ :=
  5 / (6 - 5 * r) - 5 / 6 -
    25 / (6 * (4 + 12 * t)) * (4 * r ^ 3 + 12 * t * r ^ 11)

def U2 (r : ℝ) : ℝ :=
  25 * P t r / (6 * (4 + 12 * t) * (6 - 5 * r) ^ 2)

lemma U_hasDerivAt (r : ℝ) (hr : r < 6 / 5) : HasDerivAt U (U1 r) r := by
  have hden : 6 - 5 * r ≠ 0 := by linarith
  have harg : 1 - 5 * r / 6 ≠ 0 := by linarith
  have hlog := ((hasDerivAt_const r 1).sub ((hasDerivAt_id r).const_mul (5 / 6))).log (by dsimp; linarith : 1 - (5 / 6 : ℝ) * r ≠ 0)
  have hpoly := ((hasDerivAt_id r).pow 4).add
    (((hasDerivAt_id r).pow 12).const_mul t)
  have h := (hlog.neg.sub ((hasDerivAt_id r).const_mul (5 / 6))).sub
    (hpoly.const_mul (25 / (6 * (4 + 12 * t))))
  convert h using 1 <;> try funext z
  all_goals dsimp [U, U1]
  all_goals field_simp [hden, harg, four_add_t_pos.ne'] <;> norm_num <;> ring

lemma P_factor (r : ℝ) :
    P t r = 6 * (4 + 12 * t) - (12 * r ^ 2 + 132 * t * r ^ 10) * (6 - 5 * r) ^ 2 := by
  unfold P
  ring

lemma U2_formula (r : ℝ) (hden : 6 - 5 * r ≠ 0) :
    U2 r = 25 / (6 - 5 * r) ^ 2 -
      25 / (6 * (4 + 12 * t)) * (12 * r ^ 2 + 132 * t * r ^ 10) := by
  unfold U2
  rw [← div_mul_div_comm, P_factor, sub_div,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hden), mul_sub, ← mul_div_assoc,
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) four_add_t_pos.ne')]

lemma U1_hasDerivAt (r : ℝ) (hr : r < 6 / 5) : HasDerivAt U1 (U2 r) r := by
  have hden : 6 - 5 * r ≠ 0 := by linarith
  have hrat := (hasDerivAt_const r 5).div
    ((hasDerivAt_const r 6).sub ((hasDerivAt_id r).const_mul 5)) hden
  have hpoly := (((hasDerivAt_id r).pow 3).const_mul 4).add
    (((hasDerivAt_id r).pow 11).const_mul (12 * t))
  have h := (hrat.sub_const (5 / 6)).sub
    (hpoly.const_mul (25 / (6 * (4 + 12 * t))))
  convert h using 1 <;> try funext z
  all_goals norm_num [U1, U2_formula r hden]
  all_goals ring_nf
  all_goals simp

lemma U_endpoints : U 0 = 0 ∧ U 1 = 0 ∧ U1 0 = 0 ∧ U1 1 = 0 := by
  have hl : Real.log (1 / 6 : ℝ) = -Real.log 6 := by rw [Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hparam := parameter_identity
  constructor
  · norm_num [U]
  constructor
  · norm_num [U, hl]
    calc
      Real.log 6 - 5 / 6 - 25 / (6 * (4 + 12 * t)) * (1 + t) =
          Real.log 6 - 5 / 6 - (25 / 6 : ℝ) * ((1 + t) / (4 + 12 * t)) := by field_simp [four_add_t_pos.ne']
      _ = 0 := by rw [hparam]; ring
  constructor
  · norm_num [U1]
  · norm_num [U1]
    field_simp [four_add_t_pos.ne']
    ring

/-- The actual two-atom integrated distribution function. -/
def xHat (r : ℝ) : ℝ := if r ≤ Q then C - x * r else 1 - r

def kernel (r : ℝ) : ℝ := 1 / (xHat r) ^ 2

def J (r : ℝ) : ℝ := ∫ v in (0 : ℝ)..r, kernel v

def K (r : ℝ) : ℝ := ∫ v in (0 : ℝ)..r, v * kernel v

/-- The manuscript's actual interval-integral first variation. -/
def V (r : ℝ) : ℝ := (∫ v in (0 : ℝ)..r, (r - v) / (xHat v) ^ 2) - betaSq * xi r

def V1 (r : ℝ) : ℝ := J r - betaSq * xi1 r
def V2 (r : ℝ) : ℝ := kernel r - betaSq * xi2 r

lemma xHat_continuous : Continuous xHat := by
  unfold xHat
  apply Continuous.if_le (continuous_const.sub (continuous_const.mul continuous_id))
    (continuous_const.sub continuous_id) continuous_id continuous_const
  intro r hr
  dsimp at hr
  subst r
  norm_num [C, Q, x]

lemma xHat_pos (r : ℝ) (hr : r < 1) : 0 < xHat r := by
  unfold xHat
  split_ifs with h
  · norm_num [C, x, Q] at h ⊢
    linarith
  · linarith

lemma kernel_continuousAt (r : ℝ) (hr : r < 1) : ContinuousAt kernel r := by
  exact continuousAt_const.div (xHat_continuous.continuousAt.pow 2)
    (pow_ne_zero _ (xHat_pos r hr).ne')

lemma kernel_measurable : Measurable kernel :=
  measurable_const.div (xHat_continuous.measurable.pow_const 2)

lemma kernel_continuousOn (r : ℝ) (hr : r < 1) : ContinuousOn kernel (uIcc (0 : ℝ) r) := by
  intro v hv
  apply (kernel_continuousAt v ?_).continuousWithinAt
  rcases (mem_uIcc.mp hv) with h | h
  · linarith [h.2]
  · linarith [h.2]

lemma kernel_intervalIntegrable (r : ℝ) (hr : r < 1) :
    IntervalIntegrable kernel volume 0 r := (kernel_continuousOn r hr).intervalIntegrable

lemma J_hasDerivAt (r : ℝ) (hr : r < 1) : HasDerivAt J (kernel r) r :=
  intervalIntegral.integral_hasDerivAt_right (kernel_intervalIntegrable r hr)
    kernel_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter (kernel_continuousAt r hr)

lemma K_hasDerivAt (r : ℝ) (hr : r < 1) : HasDerivAt K (r * kernel r) r := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_id.continuousOn.mul (kernel_continuousOn r hr)).intervalIntegrable
  · exact (measurable_id.mul kernel_measurable).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact continuousAt_id.mul (kernel_continuousAt r hr)

lemma V_eq_moments (r : ℝ) (hr : r < 1) :
    V r = r * J r - K r - betaSq * xi r := by
  unfold V J K
  have hk := kernel_intervalIntegrable r hr
  have hvk : IntervalIntegrable (fun v : ℝ => v * kernel v) volume 0 r :=
    (continuous_id.continuousOn.mul (kernel_continuousOn r hr)).intervalIntegrable
  have heq : (fun v : ℝ => (r - v) / (xHat v) ^ 2) =
      (fun v => r * kernel v - v * kernel v) := by funext v; unfold kernel; ring
  rw [heq, intervalIntegral.integral_sub (hk.const_mul r) hvk,
    intervalIntegral.integral_const_mul]

lemma V_hasDerivAt (r : ℝ) (hr : r < 1) : HasDerivAt V (V1 r) r := by
  have h := (((hasDerivAt_id r).mul (J_hasDerivAt r hr)).sub
    (K_hasDerivAt r hr)).sub ((xi_hasDerivAt r).const_mul betaSq)
  have hM : HasDerivAt (fun v => v * J v - K v - betaSq * xi v) (V1 r) r := by
    convert h using 1 <;> try funext z
    all_goals norm_num [V1]
  apply hM.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hr] with v hv
  exact V_eq_moments v hv

lemma V1_hasDerivAt (r : ℝ) (hr : r < 1) : HasDerivAt V1 (V2 r) r := by
  exact (J_hasDerivAt r hr).sub ((xi1_hasDerivAt r).const_mul betaSq)

lemma V_secondDerivative (r : ℝ) (hr : r < 1) : deriv (deriv V) r = V2 r := by
  have h : HasDerivAt (deriv V) (V2 r) r := by
    apply (V1_hasDerivAt r hr).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with v hv
    exact (V_hasDerivAt v hv).deriv
  exact h.deriv

/-- The exact three-region curvature certificate forces strict interior positivity. -/
theorem U_pos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < U r := by
  obtain ⟨a, d, ha, hd, had, _, _, _, _, _, houter, hinner⟩ :=
    two_simple_zeros_sign_pattern t exampleParameter_mem
  obtain ⟨h0, h1, h10, h11⟩ := U_endpoints
  apply DoubleWellPositive.positive_of_three_curvature_regions U U1 U2 a d
    (by linarith [ha.1]) had (by linarith [hd.2])
    (fun r hr => U_hasDerivAt r (by linarith [hr.2]))
    (fun r hr => U1_hasDerivAt r (by linarith [hr.2])) h0 h1 h10 h11
  · intro r hr
    have hr1 : r < 1 := by rcases hr with hr | hr <;> linarith [ha.2, hr.2]
    have hR : 0 < 6 - 5 * r := by linarith
    have hp : 0 < P t r := by
      apply houter r
      rcases hr with hr | hr
      · exact Or.inl ⟨hr.1.le, hr.2⟩
      · exact Or.inr ⟨hr.1, hr.2.le⟩
    unfold U2
    exact div_pos (mul_pos (by norm_num) hp)
      (mul_pos (mul_pos (by norm_num) four_add_t_pos) (pow_pos hR _))
  · intro r hr
    have hr1 : r < 1 := by linarith [hd.2, hr.2]
    have hR : 0 < 6 - 5 * r := by linarith
    unfold U2
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (hinner r hr))
      (mul_pos (mul_pos (by norm_num) four_add_t_pos) (pow_pos hR _))

/-- The primitive of the reciprocal-square profile below the contact. -/
def JBelow (r : ℝ) : ℝ := (1 / x) * (1 / (C - x * r) - 1 / C)

lemma affine_profile_pos (r : ℝ) (hr : r ≤ Q) : 0 < C - x * r := by
  norm_num [C, x, Q] at hr ⊢
  linarith

lemma JBelow_hasDerivAt (r : ℝ) (hr : r ≤ Q) : HasDerivAt JBelow (kernel r) r := by
  have hden := (affine_profile_pos r hr).ne'
  have h := (((hasDerivAt_const r 1).div
    ((hasDerivAt_const r C).sub ((hasDerivAt_id r).const_mul x)) hden).sub_const
    (1 / C)).const_mul (1 / x)
  convert h using 1 <;> try funext z
  all_goals dsimp [JBelow, kernel, xHat]
  all_goals simp only [ite_eq_left hr]
  all_goals field_simp [hden, x_pos.ne']
  all_goals ring

lemma J_eq_below (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Q) : J r = JBelow r := by
  have hr1 : r < 1 := hr.2.trans_lt Q_lt_one
  have hder : ∀ v ∈ uIcc (0 : ℝ) r, HasDerivAt JBelow (kernel v) v := by
    intro v hv
    rw [uIcc_of_le hr.1] at hv
    exact JBelow_hasDerivAt v (hv.2.trans hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (kernel_intervalIntegrable r hr1)
  have hz : JBelow 0 = 0 := by norm_num [JBelow, x, C]
  simpa [J, hz] using h

lemma J_at_Q : J Q = 15 := by
  rw [J_eq_below Q ⟨Q_pos.le, le_rfl⟩]
  norm_num [JBelow, C, x, Q]

/-- The explicit below-contact first variation, connected to its integral below. -/
def below (r : ℝ) : ℝ := U (r / Q) / x ^ 2

lemma below_hasDerivAt (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Q) : HasDerivAt below (V1 r) r := by
  have hrU : r / Q < 6 / 5 := by
    apply (div_lt_iff₀ Q_pos).2
    norm_num [Q] at hr ⊢
    linarith [hr.2]
  have h := ((U_hasDerivAt (r / Q) hrU).comp r
    ((hasDerivAt_id r).div_const Q)).div_const (x ^ 2)
  have hden : 6 - 5 * (r / Q) ≠ 0 := by linarith
  have haff := (affine_profile_pos r hr.2).ne'
  have hnormal27 : (27 : ℝ) - r * 25 ≠ 0 := by
    norm_num [Q] at hr
    linarith [hr.2]
  have hnormal : (27 / 5 : ℝ) - r * 5 ≠ 0 := by
    norm_num [Q] at hr
    linarith [hr.2]
  rw [V1, J_eq_below r hr]
  convert h using 1 <;> try funext z
  all_goals dsimp [below, U1, JBelow, betaSq, xi1, b]
  all_goals field_simp [hden, haff, Q_pos.ne', x_pos.ne', four_add_t_pos.ne']
  all_goals norm_num [Q, x, C]
  all_goals ring_nf
  all_goals field_simp [hnormal]
  all_goals ring_nf
  all_goals field_simp [hnormal27]
  all_goals ring

/-- Direct integration identifies the actual first-variation integral with `U`. -/
theorem V_eq_below (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Q) : V r = below r := by
  have hmem : ∀ v ∈ uIcc (0 : ℝ) r, v ∈ Icc (0 : ℝ) Q := by
    intro v hv
    rw [uIcc_of_le hr.1] at hv
    exact ⟨hv.1, hv.2.trans hr.2⟩
  have hder : ∀ v ∈ uIcc (0 : ℝ) r, HasDerivAt V (V1 v) v := fun v hv =>
    V_hasDerivAt v ((hmem v hv).2.trans_lt Q_lt_one)
  have hbder : ∀ v ∈ uIcc (0 : ℝ) r, HasDerivAt below (V1 v) v := fun v hv =>
    below_hasDerivAt v (hmem v hv)
  have hint : IntervalIntegrable V1 volume 0 r :=
    (show ContinuousOn V1 (uIcc (0 : ℝ) r) from fun v hv =>
      (V1_hasDerivAt v ((hmem v hv).2.trans_lt Q_lt_one)).continuousAt.continuousWithinAt).intervalIntegrable
  have hV := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt hbder hint
  have hz : V 0 = 0 := by norm_num [V, xi]
  have hbz : below 0 = 0 := by simp [below, U_endpoints.1]
  rw [hz, sub_zero] at hV
  rw [hbz, sub_zero] at hB
  exact hV.symm.trans hB

lemma contact_value : V Q = 0 := by
  rw [V_eq_below Q ⟨Q_pos.le, le_rfl⟩]
  simp [below, Q_pos.ne', U_endpoints.2.1]

lemma contact_derivative : deriv V Q = 0 := by
  rw [(V_hasDerivAt Q Q_lt_one).deriv]
  unfold V1
  rw [J_at_Q, contact_slope_equation]
  ring

/-- Below the contact, strict positivity holds for the actual integral function. -/
theorem V_pos_below (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) Q) : 0 < V r := by
  rw [V_eq_below r ⟨hr.1.le, hr.2.le⟩]
  have hv : r / Q ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hr.1 Q_pos, (div_lt_one₀ Q_pos).2 hr.2⟩
  exact div_pos (U_pos _ hv) (pow_pos x_pos _)


/-- The replica-symmetric residual curvature parameter at an arbitrary overlap. -/
def residualCurvature (r : ℝ) : ℝ := betaSq * (1 - r) ^ 2 * xi2 r

def residualCurvature1 (r : ℝ) : ℝ := betaSq *
  (12 * (1 - r) * r * (2 - 4 * r) +
    132 * b * (1 - r) * r ^ 9 * (10 - 12 * r))

lemma residualCurvature_hasDerivAt (r : ℝ) :
    HasDerivAt residualCurvature (residualCurvature1 r) r := by
  have h := ((((hasDerivAt_const r 1).sub (hasDerivAt_id r)).pow 2).const_mul betaSq).mul
    (xi2_hasDerivAt r)
  convert h using 1 <;> try funext z
  all_goals norm_num [residualCurvature, residualCurvature1, xi2, xi3] <;> ring

lemma residualCurvature_at_Q :
    residualCurvature Q = (12 + 132 * t) / (24 + 72 * t) := by
  rw [residualCurvature, xi2_at_Q]
  dsimp [betaSq, Q]
  have hd : 24 + t * 72 ≠ 0 := by linarith [t_pos]
  field_simp [four_add_t_pos.ne', show 24 + 72 * t ≠ 0 by linarith [t_pos]]
  ring_nf

lemma residualCurvature_Q_lt_two_thirds : residualCurvature Q < 2 / 3 := by
  have ht : t < (1 / 21 : ℝ) := lt_trans exampleParameter_enclosure.2 (by norm_num [tPlus])
  rw [residualCurvature_at_Q]
  apply (div_lt_iff₀ (by linarith [t_pos] : 0 < 24 + 72 * t)).2
  linarith

lemma residualCurvature1_neg (r : ℝ) (hr : r ∈ Ioo Q 1) : residualCurvature1 r < 0 := by
  have hrpos : 0 < r := Q_pos.trans hr.1
  have h1 : 0 < 1 - r := sub_pos.2 hr.2
  have h4 : 2 - 4 * r < 0 := by norm_num [Q] at hr; linarith [hr.1]
  have h12 : 10 - 12 * r < 0 := by norm_num [Q] at hr; linarith [hr.1]
  have hterm4 : 12 * (1 - r) * r * (2 - 4 * r) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) h1) hrpos) h4
  have hterm12 : 132 * b * (1 - r) * r ^ 9 * (10 - 12 * r) < 0 :=
    mul_neg_of_pos_of_neg
      (mul_pos (mul_pos (mul_pos (by norm_num) b_pos) h1) (pow_pos hrpos _)) h12
  exact mul_neg_of_pos_of_neg betaSq_pos (add_neg hterm4 hterm12)

lemma residualCurvature_antitone : StrictAntiOn residualCurvature (Icc Q 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (show Continuous residualCurvature from continuous_iff_continuousAt.mpr
      fun r => (residualCurvature_hasDerivAt r).continuousAt).continuousOn
  intro r hr
  rw [interior_Icc] at hr
  rw [(residualCurvature_hasDerivAt r).deriv]
  exact residualCurvature1_neg r hr

lemma xHat_above (r : ℝ) (hr : Q ≤ r) : xHat r = 1 - r := by
  unfold xHat
  split_ifs with h
  · have he : r = Q := le_antisymm h hr
    subst r
    norm_num [C, x, Q]
  · rfl

lemma V2_above_formula (r : ℝ) (hr : r ∈ Ico Q 1) :
    V2 r = (1 - residualCurvature r) / (1 - r) ^ 2 := by
  unfold V2 kernel residualCurvature
  rw [xHat_above r hr.1, sub_div]
  have he : betaSq * (1 - r) ^ 2 * xi2 r = (betaSq * xi2 r) * (1 - r) ^ 2 := by ring
  rw [he, mul_div_cancel_right₀ _ (pow_ne_zero 2 (sub_pos.2 hr.2).ne')]

/-- Above the contact the actual second derivative is strictly positive. -/
theorem V2_pos_above (r : ℝ) (hr : r ∈ Ico Q 1) : 0 < V2 r := by
  have hbound : residualCurvature r ≤ residualCurvature Q :=
    residualCurvature_antitone.antitoneOn ⟨le_rfl, Q_lt_one.le⟩ ⟨hr.1, hr.2.le⟩ hr.1
  have hcurv : residualCurvature r < 1 := lt_of_le_of_lt hbound
    (lt_trans residualCurvature_Q_lt_two_thirds (by norm_num))
  rw [V2_above_formula r hr]
  exact div_pos (sub_pos.2 hcurv) (pow_pos (sub_pos.2 hr.2) _)

lemma V1_at_Q : V1 Q = 0 := by
  unfold V1
  rw [J_at_Q, contact_slope_equation]
  ring

/-- Strict positivity above the contact follows from the actual integral derivatives. -/
theorem V_pos_above (r : ℝ) (hr : r ∈ Ioo Q 1) : 0 < V r := by
  have hmono1 : StrictMonoOn V1 (Icc Q r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (show ContinuousOn V1 (Icc Q r) from fun v hv =>
        (V1_hasDerivAt v (hv.2.trans_lt hr.2)).continuousAt.continuousWithinAt)
    intro v hv
    rw [interior_Icc] at hv
    rw [(V1_hasDerivAt v (hv.2.trans hr.2)).deriv]
    exact V2_pos_above v ⟨hv.1.le, hv.2.trans hr.2⟩
  have hmono : StrictMonoOn V (Icc Q r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (show ContinuousOn V (Icc Q r) from fun v hv =>
        (V_hasDerivAt v (hv.2.trans_lt hr.2)).continuousAt.continuousWithinAt)
    intro v hv
    rw [interior_Icc] at hv
    rw [(V_hasDerivAt v (hv.2.trans hr.2)).deriv]
    have h := hmono1 ⟨le_rfl, hr.1.le⟩ ⟨hv.1.le, hv.2.le⟩ hv.1
    simpa [V1_at_Q] using h
  have h := hmono ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1
  simpa [contact_value] using h

/-- This is the full scalar strict 1RSB contact certificate (5.11). -/
theorem strict_one_step_certificate :
    V Q = 0 ∧ deriv V Q = 0 ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q → 0 < V r) ∧
    0 < deriv (deriv V) Q := by
  refine ⟨contact_value, contact_derivative, ?_, ?_⟩
  · intro r hr hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact V_pos_below r ⟨hr.1, h⟩
    · exact V_pos_above r ⟨h, hr.2⟩
  · rw [V_secondDerivative Q Q_lt_one]
    exact V2_pos_above Q ⟨le_rfl, Q_lt_one⟩

lemma xi_secondDerivative : deriv (deriv xi) = xi2 := by
  have hd : deriv xi = xi1 := funext fun r => (xi_hasDerivAt r).deriv
  rw [hd]
  exact funext fun r => (xi1_hasDerivAt r).deriv

lemma xi2_pos (r : ℝ) (hr : 0 < r) : 0 < xi2 r := by
  unfold xi2
  have hb := b_pos
  positivity

/-- The scaled curvature witness in the manuscript. -/
def w (r : ℝ) : ℝ := 11 * b * r ^ 8

lemma curvature_numerator_identity (r : ℝ) :
    r ^ 2 * (3 * (xi3 r) ^ 2 - 2 * xi2 r * xi4 r) =
      (12 * r ^ 2) ^ 2 * 8 * (1 - 3 * w r) * (1 - 5 * w r) := by
  unfold xi2 xi3 xi4 w
  ring

lemma w_at_witness : w (5 / 6) = 11 * t * (25 / 27 : ℝ) ^ 8 := by
  norm_num [w, b]
  ring

lemma witness_w_bounds : (1 / 4 : ℝ) < w (5 / 6) ∧ w (5 / 6) < (3 / 10 : ℝ) := by
  rw [w_at_witness]
  have hp : 0 < (11 : ℝ) * (25 / 27 : ℝ) ^ 8 := by positivity
  have hlo := final_rational_comparisons.2.2.1
  have hhi := final_rational_comparisons.2.2.2
  have hlo' := mul_lt_mul_of_pos_left exampleParameter_enclosure.1 hp
  have hhi' := mul_lt_mul_of_pos_left exampleParameter_enclosure.2 hp
  constructor
  · apply lt_trans hlo
    convert hlo' using 1 <;> ring
  · apply lt_trans _ hhi
    convert hhi' using 1 <;> ring

lemma curvature_numerator_neg :
    3 * (xi3 (5 / 6)) ^ 2 - 2 * xi2 (5 / 6) * xi4 (5 / 6) < 0 := by
  have hfirst : 0 < 1 - 3 * w (5 / 6) := by linarith [witness_w_bounds.2]
  have hsecond : 1 - 5 * w (5 / 6) < 0 := by linarith [witness_w_bounds.1]
  have hprod := mul_neg_of_pos_of_neg hfirst hsecond
  have h := curvature_numerator_identity (5 / 6)
  have hneg : (12 * (5 / 6 : ℝ) ^ 2) ^ 2 * 8 *
      (1 - 3 * w (5 / 6)) * (1 - 5 * w (5 / 6)) < 0 := by
    have he : (12 * (5 / 6 : ℝ) ^ 2) ^ 2 * 8 *
        (1 - 3 * w (5 / 6)) * (1 - 5 * w (5 / 6)) =
        ((12 * (5 / 6 : ℝ) ^ 2) ^ 2 * 8) *
          ((1 - 3 * w (5 / 6)) * (1 - 5 * w (5 / 6))) := by ring
    rw [he]
    exact mul_neg_of_pos_of_neg (by norm_num) hprod
  rw [← h] at hneg
  norm_num at hneg
  linarith

/-- The actual inverse square root of `xi''` has a negative second derivative at `5/6`. -/
theorem inverse_curvature_negative :
    deriv (deriv (InverseSqrtCalculus.inverseSqrt (deriv (deriv xi)))) (5 / 6) < 0 := by
  rw [xi_secondDerivative]
  have hd : deriv xi2 = xi3 := funext fun r => (xi2_hasDerivAt r).deriv
  have hdd : deriv (deriv xi2) = xi4 := by
    rw [hd]
    exact funext fun r => (xi3_hasDerivAt r).deriv
  have hf := InverseSqrtCalculus.deriv2_inverseSqrt isOpen_Ioi
    (fun r hr => xi2_pos r hr) (fun r _ => (xi2_hasDerivAt r).differentiableAt)
    (by norm_num : (5 / 6 : ℝ) ∈ Ioi (0 : ℝ))
    (show DifferentiableAt ℝ (deriv xi2) (5 / 6) from
      hd ▸ (xi3_hasDerivAt (5 / 6)).differentiableAt)
  rw [hf, hdd, hd]
  exact div_neg_of_neg_of_pos curvature_numerator_neg
    (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.2 (xi2_pos _ (by norm_num))) _))

/-- Negative curvature contradicts convexity on the manuscript's stated domain `(0,1]`. -/
theorem inverse_not_convex :
    ¬ ConvexOn ℝ (Ioc (0 : ℝ) 1) (InverseSqrtCalculus.inverseSqrt (deriv (deriv xi))) := by
  intro hc
  have hd : ∀ r ∈ Ioc (0 : ℝ) 1,
      DifferentiableAt ℝ (InverseSqrtCalculus.inverseSqrt (deriv (deriv xi))) r := by
    intro r hr
    rw [xi_secondDerivative]
    exact (InverseSqrtCalculus.hasDerivAt_inverseSqrt (xi2_hasDerivAt r)
      (xi2_pos r hr.1)).differentiableAt
  have hm := (hc.monotoneOn_deriv hd).mono Ioo_subset_Ioc_self
  have hnonneg := hm.derivWithin_nonneg (x := (5 / 6 : ℝ))
  rw [derivWithin_of_isOpen isOpen_Ioo (by norm_num : (5 / 6 : ℝ) ∈ Ioo (0 : ℝ) 1)] at hnonneg
  linarith [inverse_curvature_negative]

/-- The quantitative nondegeneracy margin uses the actual ordinary second derivative. -/
theorem actual_contact_margin : beta ^ 2 * (1 - Q) ^ 2 * deriv (deriv xi) Q < 2 / 3 := by
  rw [beta_sq, xi_secondDerivative]
  exact residualCurvature_Q_lt_two_thirds


lemma parameters_mem : x ∈ Ioo (0 : ℝ) 1 ∧ Q ∈ Ioo (0 : ℝ) 1 := by
  norm_num [x, Q]

lemma profile_constant : C = 1 - Q + x * Q := by norm_num [C, Q, x]

lemma xi_even : Function.Even xi := by
  intro r
  unfold xi
  ring

lemma V_at_zero : V 0 = 0 := by norm_num [V, xi]

/-- The zero set of the actual interval-integral first variation is exactly `{0,Q}`. -/
theorem actual_contact_set (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
    V r = 0 ↔ r = 0 ∨ r = Q := by
  constructor
  · intro hz
    by_cases h0 : r = 0
    · exact Or.inl h0
    by_cases hQ : r = Q
    · exact Or.inr hQ
    have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm h0)
    have h := strict_one_step_certificate.2.2.1 r ⟨hr0, hr.2⟩ hQ
    linarith
  · rintro (rfl | rfl)
    · exact V_at_zero
    · exact contact_value

/-- All scalar assertions of the manuscript's nonconvex strict 1RSB example. -/
theorem nonconvex_example :
    tMinus < t ∧ t < tPlus ∧ 0 < b ∧ 0 < beta ∧
    x ∈ Ioo (0 : ℝ) 1 ∧ Q ∈ Ioo (0 : ℝ) 1 ∧
    V Q = 0 ∧ deriv V Q = 0 ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q → 0 < V r) ∧
    0 < deriv (deriv V) Q ∧
    beta ^ 2 * (1 - Q) ^ 2 * deriv (deriv xi) Q < 2 / 3 ∧
    deriv (deriv (InverseSqrtCalculus.inverseSqrt (deriv (deriv xi)))) (5 / 6) < 0 ∧
    ¬ ConvexOn ℝ (Ioc (0 : ℝ) 1) (InverseSqrtCalculus.inverseSqrt (deriv (deriv xi))) :=
  ⟨exampleParameter_enclosure.1, exampleParameter_enclosure.2, b_pos, beta_pos,
    parameters_mem.1, parameters_mem.2, strict_one_step_certificate.1,
    strict_one_step_certificate.2.1, strict_one_step_certificate.2.2.1,
    strict_one_step_certificate.2.2.2, actual_contact_margin,
    inverse_curvature_negative, inverse_not_convex⟩


end
end SlowEquilibration.NonconvexCertificate
