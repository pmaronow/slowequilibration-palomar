-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SlowEquilibration.InverseSqrtCalculus

open Set Filter
open scoped Topology

/-- The inverse square root of a real function, using the actual real square root. -/
noncomputable def inverseSqrt (v : ℝ → ℝ) : ℝ → ℝ := fun r => (Real.sqrt (v r))⁻¹

/-- First derivative at a positive differentiability point. -/
theorem hasDerivAt_inverseSqrt {v : ℝ → ℝ} {r v' : ℝ}
    (hv : HasDerivAt v v' r) (hpos : 0 < v r) :
    HasDerivAt (inverseSqrt v) (-v' / (2*(Real.sqrt (v r))^3)) r := by
  have hspos := Real.sqrt_pos.2 hpos
  have h := (hv.sqrt hpos.ne').inv hspos.ne'
  unfold inverseSqrt
  convert h using 1
  field_simp [hspos.ne']

/-- Actual first derivative, rather than a derivative supplied as a field. -/
theorem deriv_inverseSqrt {v : ℝ → ℝ} {r : ℝ}
    (hv : DifferentiableAt ℝ v r) (hpos : 0 < v r) :
    deriv (inverseSqrt v) r = -(deriv v r) / (2*(Real.sqrt (v r))^3) :=
  (hasDerivAt_inverseSqrt hv.hasDerivAt hpos).deriv

/-- The second derivative formula on an open positive twice-differentiable
region. A neighborhood differentiability hypothesis makes the local first
formula legitimate; no preassigned second derivative identity is assumed. -/
theorem deriv2_inverseSqrt {v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hpos : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ s, DifferentiableAt ℝ v r)
    {r : ℝ} (hr : r ∈ s) (hdv : DifferentiableAt ℝ (deriv v) r) :
    deriv (deriv (inverseSqrt v)) r =
      (3*(deriv v r)^2-2*v r*deriv (deriv v) r) /
        (4*(Real.sqrt (v r))^5) := by
  have hspos : 0 < Real.sqrt (v r) := Real.sqrt_pos.2 (hpos r hr)
  have hsne : Real.sqrt (v r) ≠ 0 := hspos.ne'
  have heq : deriv (inverseSqrt v) =ᶠ[nhds r]
      (fun x => -(deriv v x)/(2*(Real.sqrt (v x))^3)) := by
    filter_upwards [hs.mem_nhds hr] with x hx
    exact deriv_inverseSqrt (hv x hx) (hpos x hx)
  rw [heq.deriv_eq]
  have hsqrt := ((hv r hr).hasDerivAt).sqrt (hpos r hr).ne'
  have hden := (hsqrt.pow 3).const_mul (2:ℝ)
  have hd := (hdv.hasDerivAt.neg).div hden (by positivity : 2*(Real.sqrt (v r))^3 ≠ 0)
  have hvalue := hd.deriv
  change deriv (fun x => -(deriv v x)/(2*(Real.sqrt (v x))^3)) r = _ at hvalue
  rw [hvalue]
  have hsq := Real.sq_sqrt (hpos r hr).le
  dsimp
  have hnum : 3*(deriv v r)^2-2*v r*deriv (deriv v) r =
      3*(deriv v r)^2-2*(Real.sqrt (v r))^2*deriv (deriv v) r := by rw [hsq]
  rw [hnum]
  field_simp [hsne]
  norm_num
  ring

/-- Strict positivity of the ordinary second derivative follows from strict
positivity of its classical numerator. -/
theorem deriv2_inverseSqrt_pos {v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hpos : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ s, DifferentiableAt ℝ v r)
    {r : ℝ} (hr : r ∈ s) (hdv : DifferentiableAt ℝ (deriv v) r)
    (hcurv : 0 < 3*(deriv v r)^2-2*v r*deriv (deriv v) r) :
    0 < deriv (deriv (inverseSqrt v)) r := by
  rw [deriv2_inverseSqrt hs hpos hv hr hdv]
  have hsqrtpos := Real.sqrt_pos.2 (hpos r hr)
  exact div_pos hcurv (by positivity)

/-- Strict convexity on a convex region, including its boundary, when the
positive curvature formula holds in its interior. -/
theorem strictConvexOn_inverseSqrt {v : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hc : ContinuousOn v s) (hp : ∀ r ∈ s, 0 < v r)
    (hv : ∀ r ∈ interior s, DifferentiableAt ℝ v r)
    (hdv : ∀ r ∈ interior s, DifferentiableAt ℝ (deriv v) r)
    (hcurv : ∀ r ∈ interior s,
      0 < 3*(deriv v r)^2-2*v r*deriv (deriv v) r) :
    StrictConvexOn ℝ s (inverseSqrt v) := by
  apply strictConvexOn_of_deriv2_pos hs
  · exact (hc.sqrt).inv₀ (fun r hr => (Real.sqrt_pos.2 (hp r hr)).ne')
  · intro r hr
    simpa [Function.iterate_succ_apply] using deriv2_inverseSqrt_pos isOpen_interior
      (fun r hr => hp r (interior_subset hr)) hv hr (hdv r hr) (hcurv r hr)

end SlowEquilibration.InverseSqrtCalculus
