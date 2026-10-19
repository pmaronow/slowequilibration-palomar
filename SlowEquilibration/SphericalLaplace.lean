-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemigroupLaplace
public import SlowEquilibration.SphericalL2Semigroup

@[expose] public section

/-!
# The actual spherical Langevin Laplace operator

The integral uses the proved physical Langevin kernel and the actual Gibbs
Hilbert space. Identification with the independently constructed variational
resolvent is a further theorem, not a field in the construction.
-/

namespace SlowEquilibration.SphericalLaplace
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalL2Semigroup
open scoped InnerProductSpace NNReal
variable {N : ℕ}

def data (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    SemigroupLaplace.Data (Space μ J β) where
  P := P hN μ J β
  zero := P_zero hN μ J β
  add := P_add hN μ J β
  norm_le := P_apply_norm_le hN μ J β
  continuous := P_apply_continuous hN μ J β

def R (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    Space μ J β →L[ℝ] Space μ J β := (data hN μ J β).operator

theorem R_apply (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : Space μ J β) :
    R hN μ J β f = ∫ t : ℝ in Ioi 0, Real.exp (-t) • P hN μ J β t.toNNReal f := rfl

theorem R_norm_le (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) : ‖R hN μ J β‖ ≤ 1 := (data hN μ J β).operator_norm_le

theorem R_selfAdjoint (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) : IsSelfAdjoint (R hN μ J β) :=
  (data hN μ J β).operator_isSelfAdjoint (P_isSymmetric hN μ J β)

theorem R_nonnegative (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (f : Space μ J β) : 0 ≤ inner ℝ (R hN μ J β f) f :=
  (data hN μ J β).operator_nonnegative (P_isSymmetric hN μ J β) f

theorem R_injective (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) : Function.Injective (R hN μ J β) :=
  (data hN μ J β).operator_injective (P_isSymmetric hN μ J β)

theorem R_commutes (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (f : Space μ J β) :
    R hN μ J β (P hN μ J β t f) = P hN μ J β t (R hN μ J β f) :=
  (data hN μ J β).operator_commutes t f

theorem R_quadratic_identity (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Space μ J β) :
    inner ℝ (R hN μ J β f) f =
      ∫ t : ℝ in Ioi 0, Real.exp (-t) * ‖P hN μ J β (t.toNNReal / 2) f‖ ^ 2 :=
  (data hN μ J β).inner_operator_self_integral (P_isSymmetric hN μ J β) f

end
end SlowEquilibration.SphericalLaplace
