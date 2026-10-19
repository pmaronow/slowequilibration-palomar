-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPhysicalRadialBridge
public import SlowEquilibration.SphericalMarkedSaddleComplexity

@[expose] public section

/-! The literal source A4 radial clearance follows quantitatively from the
global marked-complexity loss at the certificate contact. -/

namespace SlowEquilibration.SphericalTAPMixedSaddleClearanceChoice
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
set_option autoImplicit false

theorem sourceRadialSaddle_contact_displacement
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) :
    sourceMarkedLeastCurvature μ Q*
      (sourceRadialSaddle μ Q e-markK μ β Q)^2 ≤
      sourceEnergyCurvature μ Q*(e-markE μ β x Q)^2 := by
  have hLower := sourceRadialSaddle_global_max μ h hnp e (markK μ β Q)
  rw [sourceContact_fixed_radial_energy_expansion μ h hnp e] at hLower
  have hUpper := sourceMarkedComplexity_global_loss μ h hnp e
    (sourceRadialSaddle μ Q e)
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
    (by have hd := h.min_degree; omega) hnp
  have hdrop : 0 ≤ sourceMarkedLeastCurvature μ Q*(e-markE μ β x Q)^2 :=
    mul_nonneg hκ.le (sq_nonneg _)
  nlinarith

/-- For any exterior interval containing the source contact in its interior,
one can choose a positive energy half-width on which the actual global
radial saddle stays at least half the contact clearance from the boundary. -/
theorem sourceRadialSaddle_nearby_half_clearance
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hm : markK μ β Q ∈ Ioo L R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        sourceRadialClearance μ β Q (Ioo L R)/2 ≤
          Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ := by
  let u := sourceRadialClearance μ β Q (Ioo L R)
  let κ := sourceMarkedLeastCurvature μ Q
  let A := sourceEnergyCurvature μ Q
  have hu : 0 < u := sourceRadialClearance_pos μ hm
  have hκ : 0 < κ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
    (by have hd := h.min_degree; omega) hnp
  have hA : 0 < A := sourceEnergyCurvature_pos μ h.overlap_range.1 hnp
  let ε := min 1 (κ*u^2/(8*A))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ κ*u^2/(8*A) := min_le_right _ _
  refine ⟨ε,hε,?_⟩
  intro e he
  let d := e-markE μ β x Q
  let v := sourceRadialSaddle μ Q e-markK μ β Q
  have hd : |d| ≤ ε := abs_le.mpr (by constructor <;> dsimp [d] <;> linarith [he.1,he.2])
  have hd2 : d^2 ≤ ε := by
    have hsq := pow_le_pow_left₀ (abs_nonneg d) hd 2
    rw [sq_abs] at hsq
    nlinarith [hε1,hε]
  have hv := sourceRadialSaddle_contact_displacement μ h hnp e
  change κ*v^2 ≤ A*d^2 at hv
  have hvsmall : |v| < u/2 := by
    by_contra hn
    have hlarge : u/2 ≤ |v| := le_of_not_gt hn
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ u/2) hlarge 2
    rw [sq_abs] at hsq
    have hbound : A*d^2 ≤ κ*u^2/8 := by
      have hh := mul_le_mul_of_nonneg_left hd2 hA.le
      have hh' := mul_le_mul_of_nonneg_left hε2 hA.le
      have hcancel : A*(κ*u^2/(8*A))=κ*u^2/8 := by field_simp
      rw [hcancel] at hh'
      exact hh.trans hh'
    have hmul := mul_le_mul_of_nonneg_left hsq hκ.le
    have hstrict : 0 < κ*u^2 := mul_pos hκ (sq_pos_of_pos hu)
    nlinarith
  have hdist := Metric.infDist_le_infDist_add_dist
    (x := markK μ β Q) (y := sourceRadialSaddle μ Q e)
    (s := (Ioo L R)ᶜ)
  change u ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ+
    dist (markK μ β Q) (sourceRadialSaddle μ Q e) at hdist
  rw [Real.dist_eq] at hdist
  rw [abs_sub_comm] at hdist
  change u ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ+|v| at hdist
  linarith

end
end SlowEquilibration.SphericalTAPMixedSaddleClearanceChoice
