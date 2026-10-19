-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! # Derivative convergence from a touching differentiable upper trial

Only the pressure at the unperturbed parameter must converge. Pointwise
limsup bounds by a differentiable trial nearby and convexity squeeze its
derivatives. A full pressure limit at perturbed parameters is unnecessary.
-/
namespace SlowEquilibration.ConvexTouchDerivative
open Set Filter
open scoped Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Convex finite-volume functions touching a differentiable upper trial
at a single interior point have convergent derivatives there. The nearby
input is solely a pointwise asymptotic upper bound. -/
theorem tendsto_derivatives_of_touching_upper_trial
    {A : Type*} {l : Filter A} (p : A → ℝ → ℝ) (d : A → ℝ)
    (f : ℝ → ℝ) (x₀ δ f' : ℝ) (hδ : 0 < δ)
    (hconvex : ∀ a, ConvexOn ℝ (Icc (x₀-δ) (x₀+δ)) (p a))
    (hderiv : ∀ a, HasDerivAt (p a) (d a) x₀)
    (htrial : HasDerivAt f f' x₀)
    (htouch : Tendsto (fun a => p a x₀) l (𝓝 (f x₀)))
    (hupper : ∀ x ∈ Ioo (x₀-δ) (x₀+δ), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ a in l, p a x ≤ f x+ε) :
    Tendsto d l (𝓝 f') := by
  have hx₀ : x₀ ∈ Icc (x₀-δ) (x₀+δ) := ⟨by linarith,by linarith⟩
  obtain ⟨hleft,hright⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp htrial
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hs : ∀ᶠ x in 𝓝[<] x₀, b < slope f x₀ x :=
      hleft.eventually (lt_mem_nhds hb)
    have hn : ∀ᶠ x in 𝓝[<] x₀, x₀-δ < x :=
      (lt_mem_nhds (show x₀-δ < x₀ by linarith)).filter_mono nhdsWithin_le_nhds
    have hxevent : ∀ᶠ x in 𝓝[<] x₀, x < x₀ := self_mem_nhdsWithin
    obtain ⟨x,hx,hxn,hxs⟩ := (hxevent.and (hn.and hs)).exists
    change x < x₀ at hx
    have hxs' : b < (f x₀-f x)/(x₀-x) := by
      rw [slope_comm,slope_def_field] at hxs
      exact hxs
    let ε := ((f x₀-f x)/(x₀-x)-b)*(x₀-x)/4
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hpoint : x ∈ Ioo (x₀-δ) (x₀+δ) := ⟨hxn,by linarith⟩
    have hcenter := htouch.eventually (lt_mem_nhds (show f x₀-ε < f x₀ by linarith))
    filter_upwards [hupper x hpoint ε hε,hcenter] with a hau hac
    have hsecant := (hconvex a).slope_le_of_hasDerivAt
      ⟨hxn.le,by linarith⟩ hx₀ hx (hderiv a)
    rw [slope_def_field] at hsecant
    have hden : 0 < x₀-x := sub_pos.mpr hx
    have hmul := (div_le_iff₀ hden).mp hsecant
    have htrialmul : b*(x₀-x)+4*ε=f x₀-f x := by
      dsimp only [ε]
      field_simp
      ring
    nlinarith
  · intro b hb
    have hs : ∀ᶠ x in 𝓝[>] x₀, slope f x₀ x < b :=
      hright.eventually (gt_mem_nhds hb)
    have hn : ∀ᶠ x in 𝓝[>] x₀, x < x₀+δ :=
      (gt_mem_nhds (show x₀ < x₀+δ by linarith)).filter_mono nhdsWithin_le_nhds
    have hxevent : ∀ᶠ x in 𝓝[>] x₀, x₀ < x := self_mem_nhdsWithin
    obtain ⟨x,hx,hxn,hxs⟩ := (hxevent.and (hn.and hs)).exists
    change x₀ < x at hx
    have hxs' : (f x-f x₀)/(x-x₀) < b := by
      rw [slope_def_field] at hxs
      exact hxs
    let ε := (b-(f x-f x₀)/(x-x₀))*(x-x₀)/4
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hpoint : x ∈ Ioo (x₀-δ) (x₀+δ) := ⟨by linarith,hxn⟩
    have hcenter := htouch.eventually (lt_mem_nhds (show f x₀-ε < f x₀ by linarith))
    filter_upwards [hupper x hpoint ε hε,hcenter] with a hau hac
    have hsecant := (hconvex a).le_slope_of_hasDerivAt
      hx₀ ⟨by linarith,hxn.le⟩ hx (hderiv a)
    rw [slope_def_field] at hsecant
    have hden : 0 < x-x₀ := sub_pos.mpr hx
    have hmul := (le_div_iff₀ hden).mp hsecant
    have htrialmul : b*(x-x₀)-4*ε=f x-f x₀ := by
      dsimp only [ε]
      field_simp
      ring
    nlinarith

end SlowEquilibration.ConvexTouchDerivative
