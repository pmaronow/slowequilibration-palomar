-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundPrimalStationarity
public import SlowEquilibration.SphericalParisiOneStepDualScalar
public import SlowEquilibration.SphericalParisiPositivePolynomialCalculus

/-! A genuine global one-step primal/dual comparison. The coupled
parameters are selected from the proved global primal minimum; the
stationarity equations and positive dual margin are conclusions. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiGlobalPrimalDual
open Set SphericalParisiLabeledCovariance SphericalParisiOneStepDualScalar
open LatitudeGroundTrial
set_option maxHeartbeats 600000
variable {σ : Type*} [Fintype σ]

theorem exists_dual_below_all_primal (d : σ → ℕ) (c : σ → ℝ) {α : ℝ}
    (hα : 0 < α)
    (hd : ∀ t, HasDerivAt (xi d c) (xi1 d c t) t)
    (hmono : MonotoneOn (xi d c) (Icc (0 : ℝ) 1))
    (h1 : 0 < xi1 d c 1) (h0 : 0 ≤ xi1 d c 0) :
    ∃ q ∈ Icc (0 : ℝ) 1, ∃ κ > 0,
      0 < κ-α*(xi1 d c 1-xi1 d c q) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ L : ℝ, 0 < L-α*(1-s) →
        oneStepDual d c α q κ ≤ primal (xi d c) (xi1 d c) L α s := by
  obtain ⟨q,hq,b,hb,hmin,hQ,hDelta⟩ :=
    exists_coupled_primal_minimum (xi d c) (xi1 d c) hα hd hmono h1 h0
  let L := b+α*(1-q)
  have hL : 0 < L := by
    have hn := mul_nonneg hα.le (sub_nonneg.mpr hq.2)
    dsimp [L]
    linarith
  have hB : b=L-α*(1-q) := by dsimp [L];ring
  have hmargin := stationary_dual_margin d c hL hb hB hDelta
  have he := stationary_dual_eq_primal_expression d c hα hL hb hB hQ hDelta
  have heP : oneStepDual d c α q (1/b)=primalAtBottom (xi d c) (xi1 d c) α q b := by
    rw [primalAtBottom_eq]
    exact he
  refine ⟨q,hq,1/b,one_div_pos.mpr hb,?_,?_⟩
  · rw [hmargin]
    exact one_div_pos.mpr hL
  · intro s hs L' hL'
    rw [heP]
    have hm := hmin s hs (L'-α*(1-s)) hL'
    have hf : primalAtBottom (xi d c) (xi1 d c) α s (L'-α*(1-s))=
        primal (xi d c) (xi1 d c) L' α s := by
      unfold primalAtBottom
      rw [sub_add_cancel]
    exact hm.trans_eq hf

/-- Actual nonnegative finite covariance: all analytic conditions are
proved from the literal polynomial, with arbitrary linear and odd terms. -/
theorem exists_positive_covariance_dual_below_all_primal
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) {α : ℝ}
    (hα : 0 < α) (h1 : 0 < xi1 d c 1) :
    ∃ q ∈ Icc (0 : ℝ) 1, ∃ κ > 0,
      0 < κ-α*(xi1 d c 1-xi1 d c q) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ L : ℝ, 0 < L-α*(1-s) →
        oneStepDual d c α q κ ≤ primal (xi d c) (xi1 d c) L α s :=
  exists_dual_below_all_primal d c hα
    (SphericalParisiPositivePolynomialCalculus.xi_hasDerivAt d c)
    (SphericalParisiPositivePolynomialCalculus.xi_monotoneOn_unitInterval d c hc)
    h1 (SphericalParisiPositivePolynomialCalculus.xi1_zero_nonnegative d c hc)

end SlowEquilibration.SphericalParisiGlobalPrimalDual
