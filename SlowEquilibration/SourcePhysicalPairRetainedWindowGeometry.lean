-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMaximumFirstMoments
public import SlowEquilibration.NatLogSequenceScales

/-! Actual contact marks admit the printed microscopic score band, and
the genuine logarithmically centered physical windows eventually lie in
each fixed positive coarse energy neighborhood. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open NatLogWindowScales
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_contact_score_neighborhood (μ:FiniteMixture) {β x Q:ℝ}
    (h:Certificate μ β x Q) (hnp:μ.minDegree<μ.maxDegree) :
    ∃ ρ:ℝ,0<ρ ∧ ∀ e k:ℝ,|e-markE μ β x Q| ≤ ρ → |k-markK μ β Q| ≤ ρ →
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2:=by
  let A:=sourceEnergyCurvature μ Q
  let B:=(((μ.scoreCovariance Q)⁻¹) 0 1+((μ.scoreCovariance Q)⁻¹) 1 0)/2
  let M:=|A|+|B|+1
  let τ:=min ((β*x)/2) ((β-β*x)/2)
  have hc:0<β*x:=mul_pos h.beta_pos h.weight_range.1
  have hx:0<β-β*x:=by nlinarith [h.beta_pos,h.weight_range.2]
  have hτ:0<τ:=lt_min (half_pos hc) (half_pos hx)
  have hM:0<M:=by dsimp [M];positivity
  let ρ:=τ/M
  have hρ:0<ρ:=div_pos hτ hM
  refine ⟨ρ,hρ,?_⟩
  intro e k he hk
  have heq:sourceEnergySlope μ Q e k-sourceEnergySlope μ Q (markE μ β x Q) (markK μ β Q)=
      A*(e-markE μ β x Q)+B*(k-markK μ β Q):=by unfold sourceEnergySlope;dsimp [A,B];ring
  have hv:|sourceEnergySlope μ Q e k-β*x| ≤ τ:=by
    rw [←sourceEnergySlope_at_contact μ h hnp,heq]
    calc
      _ ≤ |A*(e-markE μ β x Q)|+|B*(k-markK μ β Q)|:=abs_add_le _ _
      _ = |A| *|e-markE μ β x Q|+|B| *|k-markK μ β Q|:=by rw [abs_mul,abs_mul]
      _ ≤ |A| *ρ+|B| *ρ:=add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg A))
        (mul_le_mul_of_nonneg_left hk (abs_nonneg B))
      _ ≤ M*ρ:=by dsimp [M];nlinarith
      _ = τ:=by dsimp [ρ];field_simp
  have hτ1:τ ≤ (β*x)/2:=min_le_left _ _
  have hτ2:τ ≤ (β-β*x)/2:=min_le_right _ _
  constructor <;> linarith [abs_le.mp hv]

theorem source_logarithmic_center_offset_bounds {E c M δ:ℝ} (hc:0<c) (hM:0 ≤ M)
    (hδ:0<δ) (m:ℕ→ℝ)
    (hm:∀ᶠ n:ℕ in atTop,|m n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*c))| ≤ M)
    (a b:ℝ) :
    ∀ᶠ n:ℕ in atTop,(n+2:ℕ)*(E-δ) ≤ m n+a ∧ m n+b ≤ (n+2:ℕ)*(E+δ):=by
  have hLog:=normalized_center_log_bounded hc hM m hm
  have hRatio:=log_bounded_sequence_div_dimension_tendsto_zero
    (show 0 ≤ 1/(2*c)+1 by positivity) (fun n=>m n-(n+2:ℕ)*E) hLog
  have hN:Tendsto (fun n:ℕ=>((n+2:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hInv: Tendsto (fun n:ℕ=>(((n+2:ℕ):ℝ))⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp hN
  have ha:Tendsto (fun n:ℕ=>(m n-(n+2:ℕ)*E+a)/(n+2:ℕ)) atTop (𝓝 0):=by
    simpa only [add_div,div_eq_mul_inv,add_mul,mul_zero,zero_add] using hRatio.add (hInv.const_mul a)
  have hb:Tendsto (fun n:ℕ=>(m n-(n+2:ℕ)*E+b)/(n+2:ℕ)) atTop (𝓝 0):=by
    simpa only [add_div,div_eq_mul_inv,add_mul,mul_zero,zero_add] using hRatio.add (hInv.const_mul b)
  filter_upwards [ha.eventually_const_lt (show -δ<0 by linarith),hb.eventually (gt_mem_nhds hδ)] with n hn1 hn2
  have hN':(0:ℝ)<(n+2:ℕ):=by positivity
  have h1:=(lt_div_iff₀ hN').mp hn1
  have h2:=(div_lt_iff₀ hN').mp hn2
  constructor <;> nlinarith

lemma source_physical_window_subset_coarse {n:ℕ} {E δ L R l r:ℝ}
    (hl:(n+2:ℕ)*(E-δ) ≤ l) (hr:r ≤ (n+2:ℕ)*(E+δ)) :
    physicalEnergyWindow (n+2) (Icc l r) (Ioo L R) ⊆
      {b:EuclideanSpace ℝ (Fin 2)|b 0 ∈ Icc (E-δ) (E+δ) ∧ b 1 ∈ Icc L R}:=by
  intro b hb
  change (n+2:ℕ)*b 0 ∈ Icc l r ∧ b 1 ∈ Ioo L R at hb
  refine ⟨?_,⟨hb.2.1.le,hb.2.2.le⟩⟩
  have hN:(0:ℝ)<(n+2:ℕ):=by positivity
  constructor
  · exact (mul_le_mul_iff_right₀ hN).mp (hl.trans hb.1.1)
  · exact (mul_le_mul_iff_right₀ hN).mp (hb.1.2.trans hr)

end
end SlowEquilibration.PairConditionalDeterminantMoments
