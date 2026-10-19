-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGuerraBound
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

namespace SlowEquilibration.FiniteMixture

noncomputable section
open Set

set_option backward.isDefEq.respectTransparency false

/-- An even finite mixture has a convex covariance on the whole real line. -/
theorem convexOn_xi_of_even (μ : FiniteMixture)
    (he : ∀ p ∈ μ.coeff.support, Even p) : ConvexOn ℝ univ μ.xi := by
  have hsum : ∀ s : Finset ℕ, (∀ p ∈ s, Even p) →
      ConvexOn ℝ univ (fun r : ℝ => ∑ p ∈ s, μ.coeff p * r ^ p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set ℝ)))
    | @insert p s hp ih =>
      intro hs
      have hpow : ConvexOn ℝ univ (fun r : ℝ => μ.coeff p * r ^ p) := by
        simpa only [smul_eq_mul] using
          ConvexOn.smul (μ.nonneg p) ((hs p (Finset.mem_insert_self p s)).convexOn_pow (𝕜 := ℝ))
      have hrest := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      exact (hpow.add hrest).congr (fun r _ => by
        simp only [Pi.add_apply, Finset.sum_insert hp])
  exact hsum μ.coeff.support he

/-- The even-mixture covariance satisfies the spherical Guerra convexity condition. -/
theorem convexOn_xi_Icc_of_even (μ : FiniteMixture)
    (he : ∀ p ∈ μ.coeff.support, Even p) : ConvexOn ℝ (Icc (-1) 1) μ.xi :=
  (μ.convexOn_xi_of_even he).subset (subset_univ _) (convex_Icc (-1) 1)

end

end SlowEquilibration.FiniteMixture
