-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Quadratic Laplace envelopes proved directly from ordinary scalar
first and second derivatives at a stationary radial mark. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialQuadraticBounds
open Set
set_option maxHeartbeats 300000

/-- A differentiable stationary point of a concave scalar profile is a true
maximum on its entire convex domain. -/
theorem concave_max_of_stationary {f : ℝ → ℝ} {D : Set ℝ} {m : ℝ}
    (hc : ConcaveOn ℝ D f) (hm : m∈D) (hd : HasDerivAt f 0 m) :
    ∀ x∈D,f x ≤ f m := by
  intro x hx
  rcases lt_trichotomy x m with hxm|rfl|hmx
  · have hs := hc.neg.slope_le_of_hasDerivAt hx hm hxm hd.neg
    simp only [slope_def_field,Pi.neg_apply,neg_sub_neg,neg_zero] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr hxm)).mp hs
    linarith
  · exact le_rfl
  · have hs := hc.neg.le_slope_of_hasDerivAt hm hx hmx hd.neg
    simp only [slope_def_field,Pi.neg_apply,neg_sub_neg,neg_zero] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr hmx)).mp hs
    linarith

/-- An actual scalar curvature upper bound integrates to a Gaussian
quadratic upper envelope; the coefficient is not assumed to be positive. -/
theorem quadratic_upper_of_second_derivative {f g g' : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hf : ∀ x∈D,HasDerivAt f (g x) x)
    (hg : ∀ x∈D,HasDerivAt g (g' x) x) {a m : ℝ} (hm : m∈D)
    (hs : g m=0) (hSecond : ∀ x∈D,g' x ≤ -a) :
    ∀ x∈D,f x ≤ f m-a/2*(x-m)^2 := by
  let F := fun x : ℝ => f x+a/2*(x-m)^2
  let G := fun x : ℝ => g x+a*(x-m)
  let G' := fun x : ℝ => g' x+a
  have hF (x : ℝ) (hx : x∈D) : HasDerivAt F (G x) x := by
    have hquad := (((hasDerivAt_id x).sub_const m).pow 2).const_mul (a/2)
    convert (hf x hx).add hquad using 1
    · rfl
    · dsimp [G]
      simp only [pow_one]
      ring
  have hG (x : ℝ) (hx : x∈D) : HasDerivAt G (G' x) x := by
    convert (hg x hx).add (((hasDerivAt_id x).sub_const m).const_mul a) using 1
    · rfl
    · dsimp [G']
      ring
  have hConcave : ConcaveOn ℝ D F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos hD
      (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hF x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hG x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    dsimp [G']
    linarith [hSecond x (interior_subset hx)]
  have hStationary : HasDerivAt F 0 m := by
    simpa only [G,sub_self,mul_zero,hs,add_zero] using hF m hm
  intro x hx
  have hh := concave_max_of_stationary hConcave hm hStationary x hx
  dsimp [F] at hh
  simp only [sub_self,zero_pow (by norm_num : 2≠0),mul_zero,add_zero] at hh
  linarith

/-- The lower scalar curvature estimate gives the matching lower envelope. -/
theorem quadratic_lower_of_second_derivative {f g g' : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hf : ∀ x∈D,HasDerivAt f (g x) x)
    (hg : ∀ x∈D,HasDerivAt g (g' x) x) {b m : ℝ} (hm : m∈D)
    (hs : g m=0) (hSecond : ∀ x∈D,-b ≤ g' x) :
    ∀ x∈D,f m-b/2*(x-m)^2 ≤ f x := by
  have hh := quadratic_upper_of_second_derivative (f := -f) (g := -g) (g' := -g')
    hD (fun x hx => (hf x hx).neg) (fun x hx => (hg x hx).neg) (a := -b) hm
    (by simp only [Pi.neg_apply,hs,neg_zero]) (fun x hx => by
      simp only [Pi.neg_apply,neg_neg]
      linarith [hSecond x hx])
  intro x hx
  have hb := hh x hx
  simp only [Pi.neg_apply] at hb
  linarith
end SlowEquilibration.RadialQuadraticBounds
