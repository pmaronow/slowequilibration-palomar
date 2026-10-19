-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalClippedResolventL2

/-! The true outside-edge one-border Schur multiplier. Its closed form,
positivity and compact-window bounds follow from the actual semicircle
resolvent already identified from its density integral. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Set OAI.CriticalSK
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- The limiting physical Schur complement k - b m_b(k). -/
def physicalSchurMultiplier (b k : ℝ) : ℝ := k-b*physicalResolvent b k

lemma physicalResolvent_pos {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b < k) :
    0 < physicalResolvent b k := by
  have hs : 0 < k/Real.sqrt b-2 := by
    have hh:=(lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hk
    linarith
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)) (semicircleResolvent_pos hs)

lemma physicalResolvent_le_inverse_sqrt {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b ≤ k) :
    physicalResolvent b k ≤ (Real.sqrt b)⁻¹ := by
  have hs : 0 ≤ k/Real.sqrt b-2 := by
    have hh:=(le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hk
    linarith
  exact (mul_le_mul_of_nonneg_left (semicircleResolvent_le_one hs) (by positivity)).trans_eq (mul_one _)

/-- The literal physical transform equals the smaller quadratic root. -/
theorem physicalResolvent_closed_form {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b < k) :
    physicalResolvent b k=(k-Real.sqrt (k^2-4*b))/(2*b) := by
  let q:=Real.sqrt b
  let s:=k/q-2
  have hq : 0 < q:=Real.sqrt_pos.mpr hb
  have hq2 : q^2=b:=Real.sq_sqrt hb.le
  have hs : 0 < s := by
    have hh:=(lt_div_iff₀ hq).mpr hk
    dsimp only [s]
    linarith
  have hd : 0 ≤ s*(4+s):=le_of_lt (semicircle_discriminant_pos hs)
  have hk2 : 0 ≤ k^2-4*b := by
    dsimp only [q] at hq2
    nlinarith [Real.sqrt_nonneg b]
  have hscale : q^2*(s*(4+s))=k^2-4*b := by
    dsimp only [s]
    field_simp
    nlinarith [hq2]
  have hroot : q*Real.sqrt (s*(4+s))=Real.sqrt (k^2-4*b) := by
    apply (sq_eq_sq₀ (mul_nonneg hq.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hd,Real.sq_sqrt hk2,hscale]
  change q⁻¹*semicircleResolvent s=_
  unfold semicircleResolvent
  rw [← hroot]
  rw [← hq2]
  dsimp only [s]
  field_simp
  ring

/-- The limiting multiplier is the larger quadratic root, with its own
physical normalization b and no asymptotic premise. -/
theorem physicalSchurMultiplier_closed_form {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b < k) :
    physicalSchurMultiplier b k=(k+Real.sqrt (k^2-4*b))/2 := by
  rw [physicalSchurMultiplier,physicalResolvent_closed_form hb hk]
  field_simp
  ring

lemma physicalSchurMultiplier_continuous (b : ℝ) : Continuous (physicalSchurMultiplier b) := by
  exact continuous_id.sub (continuous_const.mul (physicalResolvent_continuous_shift b))

/-- The positive one-border multiplier lies between k/2 and k. -/
theorem physicalSchurMultiplier_bounds {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b < k) :
    k/2 ≤ physicalSchurMultiplier b k ∧ physicalSchurMultiplier b k ≤ k := by
  constructor
  · rw [physicalSchurMultiplier_closed_form hb hk]
    linarith [Real.sqrt_nonneg (k^2-4*b)]
  · unfold physicalSchurMultiplier
    linarith [mul_pos hb (physicalResolvent_pos hb hk)]

lemma physicalSchurMultiplier_pos {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b < k) :
    0 < physicalSchurMultiplier b k := by
  have hkp : 0 < k:=lt_trans (by positivity) hk
  exact lt_of_lt_of_le (by positivity : 0 < k/2) (physicalSchurMultiplier_bounds hb hk).1

/-- Uniform positive lower and finite upper bounds on an actual compact
outside-edge shift window. -/
theorem physicalSchurMultiplier_compact_bounds {b k0 k1 : ℝ} (hb : 0 < b)
    (hk0 : 2*Real.sqrt b < k0) (k : ℝ) (hk : k∈Icc k0 k1) :
    0 < k0/2 ∧ k0/2 ≤ physicalSchurMultiplier b k ∧ physicalSchurMultiplier b k ≤ k1 := by
  have hkp : 0 < k0:=lt_trans (by positivity) hk0
  have hBounds:=physicalSchurMultiplier_bounds hb (lt_of_lt_of_le hk0 hk.1)
  exact ⟨by positivity,le_trans (by linarith [hk.1]) hBounds.1,le_trans hBounds.2 hk.2⟩

/-- The reciprocal normalization used in determinant transfer is uniformly
bounded on every compact window strictly above the physical edge. -/
theorem physicalSchurMultiplier_compact_inverse_bound {b k0 k1 : ℝ} (hb : 0 < b)
    (hk0 : 2*Real.sqrt b < k0) (k : ℝ) (hk : k∈Icc k0 k1) :
    (physicalSchurMultiplier b k)⁻¹ ≤ 2/k0 := by
  have hh:=physicalSchurMultiplier_compact_bounds hb hk0 k hk
  calc
    _ ≤ (k0/2)⁻¹:=inv_anti₀ hh.1 hh.2.1
    _=2/k0:=by field_simp

end
end SlowEquilibration.GOEClippedResolvent
