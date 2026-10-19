-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCapFrameCount

/-! Actual indexed exponential eigenvalue bounds from the literal cap
frame. Every dimension threshold depends only on the fixed scalar margins;
it is uniform over the ordinary potential and good-reference set. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalCapFrameCount

open MeasureTheory Set Filter
open SphericalModel SphericalForm SphericalCapCutoff
open scoped Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

theorem eigenvalue_le_of_cutoff_count (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (Λ : ℝ) (k : ℕ)
    (hk : k + 1 ≤ (cutoffIndices hN β H hH Λ).card) :
    (normalizedSphericalSpectralData hN β H hH).eigenvalue k ≤ Λ := by
  classical
  by_contra hnot
  have hsub : cutoffIndices hN β H hH Λ ⊆ Finset.range k := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hjk
    have hkj : k ≤ j := le_of_not_gt hjk
    have he := (normalizedSphericalSpectralData hN β H hH).generator_monotone hkj
    have hjΛ := (mem_cutoffIndices hN β H hH Λ j).mp hj
    exact hnot (he.trans hjΛ)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  omega

private lemma exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a * N)) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply, neg_mul]

theorem energyRatio_cutoff_eventually_small {q₁ q₂ barrier δ σ : ℝ}
    (hq : q₁ < q₂) (hσ : σ < barrier - 4 * δ) :
    ∀ᶠ N : ℕ in atTop,
      energyRatio N q₁ q₂ barrier δ / Real.exp (-σ * N) ≤ 1 / 2 := by
  have ha : 0 < barrier - 4 * δ - σ := sub_pos.mpr hσ
  have hd := (exp_decay ha).const_mul (4 / (q₂-q₁)^2)
  simp only [mul_zero] at hd
  filter_upwards [eventually_ge_atTop 1,
    hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with N hN hsmall
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN1
  have hg : 0 < (q₂-q₁)^2 := sq_pos_of_pos (sub_pos.mpr hq)
  have hK : collarCoefficient N q₁ q₂ ≤ 4 / (q₂-q₁)^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hg
    nlinarith
  have heq : energyRatio N q₁ q₂ barrier δ / Real.exp (-σ * N) =
      collarCoefficient N q₁ q₂ * Real.exp (-(barrier - 4 * δ - σ) * N) := by
    unfold energyRatio
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le).trans hsmall.le

theorem exponential_count_eventually_exceeds_index {κ rate : ℝ}
    (hκ : 0 < κ) (hgap : κ < rate) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (κ * N) + 1 ≤ (1 / 4 : ℝ) * Real.exp (rate * N) := by
  have hr : 0 < rate := hκ.trans hgap
  have hgap' : 0 < rate - κ := sub_pos.mpr hgap
  have hgrowth : Tendsto (fun N : ℕ => Real.exp ((rate - κ) * N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hgap')
  have hlarge : Tendsto (fun N : ℕ => Real.exp (rate * N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hr)
  filter_upwards [hgrowth.eventually_ge_atTop 8, hlarge.eventually_ge_atTop 8] with N hG hR
  have hmul := mul_le_mul_of_nonneg_right hG (Real.exp_pos (κ * N)).le
  have heq : Real.exp ((rate - κ) * N) * Real.exp (κ * N) = Real.exp (rate * N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  linarith

/-- Exponential spectral scale and exponential mode-count scale are
independent, exactly as stated after `lem:inf-frame`. This is a deterministic
consequence of its actual cap/core/collar premises, uniform in all potentials. -/
theorem cap_indicator_index_eventually {q₁ q₂ J barrier δ c κ σ : ℝ}
    (hq : q₁ < q₂) (hκ : 0 < κ) (hκc : κ < c - 4 * δ)
    (hσ : σ < barrier - 4 * δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (hN : 2 ≤ N) (β : ℝ)
      (H : Vector N → ℝ) (hHC : ContDiff ℝ 1 H)
      (G : Set (Vector N)) (_ : MeasurableSet G),
      1 / 2 ≤ (gibbsLaw N β H).real G →
      (∀ u ∈ G, (gibbsLaw N β H).real (cap u q₁) ≤ Real.exp (-(N : ℝ) * (J - 2 * δ))) →
      (∀ u ∈ G, Real.exp (-(N : ℝ) * (J + 2 * δ)) ≤ (gibbsLaw N β H).real (cap u q₂)) →
      (∀ u ∈ G, (gibbsLaw N β H).real (collar u q₁ q₂) ≤
        Real.exp (-(N : ℝ) * (J + barrier - 2 * δ))) →
      (∀ x, SphericalAging.HardSphereDynamics.OnSphere x →
        (gibbsLaw N β H).real (cap x q₁) ≤ Real.exp (-c * N)) →
      (normalizedSphericalSpectralData hN β H hHC.continuous).eigenvalue
        (Nat.floor (Real.exp (κ * N))) ≤ Real.exp (-σ * N) := by
  filter_upwards [energyRatio_cutoff_eventually_small hq hσ,
    exponential_count_eventually_exceeds_index hκ hκc] with N hRatio hSize
  intro hN β H hHC G hG hMass hOuter hInner hCollar hColumn
  have hpos : 0 < Real.exp (-σ * N) := Real.exp_pos _
  have hrΛ : energyRatio N q₁ q₂ barrier δ < Real.exp (-σ * N) := by
    have ht := (div_le_iff₀ hpos).mp hRatio
    linarith
  have hcount := cap_indicator_count hN β H hHC G hG hq hMass hOuter hInner hCollar hColumn hrΛ
  have hfactor : (1 / 2 : ℝ) ≤ 1 - energyRatio N q₁ q₂ barrier δ / Real.exp (-σ * N) := by linarith
  have hmode : (1 / 4 : ℝ) * Real.exp ((N : ℝ) * (c - 4 * δ)) ≤
      ((cutoffIndices hN β H hHC.continuous (Real.exp (-σ * N))).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (show 0 ≤ (1 / 2 : ℝ) * Real.exp ((N : ℝ) * (c - 4 * δ)) by positivity)
    have ht : (1 / 4 : ℝ) * Real.exp ((N : ℝ) * (c - 4 * δ)) ≤
        (1 - energyRatio N q₁ q₂ barrier δ / Real.exp (-σ * N)) * (1 / 2) *
          Real.exp ((N : ℝ) * (c - 4 * δ)) := by
      convert hmul using 1 <;> ring
    exact ht.trans hcount
  have hfloor := Nat.floor_le (Real.exp_pos (κ * N)).le
  have hSize' : Real.exp (κ * N) + 1 ≤ (1 / 4 : ℝ) * Real.exp ((N : ℝ) * (c - 4 * δ)) := by
    simpa only [mul_comm (c - 4 * δ)] using hSize
  have hkreal : (Nat.floor (Real.exp (κ * N)) : ℝ) + 1 ≤
      ((cutoffIndices hN β H hHC.continuous (Real.exp (-σ * N))).card : ℝ) := by linarith
  apply eigenvalue_le_of_cutoff_count hN β H hHC.continuous _ _
  exact_mod_cast hkreal

end SlowEquilibration.SphericalCapFrameCount
