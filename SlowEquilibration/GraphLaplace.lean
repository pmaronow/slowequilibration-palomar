-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemigroupLaplace
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# A bounded graph trajectory solves the actual weak resolvent equation

The energy is the difference between graph and ambient Hilbert pairings.
The scalar weak evolution equation is integrated by the improper fundamental
theorem of calculus; the Bochner Laplace integral equals the actual adjoint
solution. No resolvent equality is assumed.
-/

namespace SlowEquilibration.GraphLaplace
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def integrand (z : ℝ → G) (t : ℝ) : G := Real.exp (-t) • z t

omit [CompleteSpace G] in
theorem integrand_integrable (z : ℝ → G) (hz : Continuous z) (C : ℝ)
    (hbound : ∀ t, 0 ≤ t → ‖z t‖ ≤ C) : IntegrableOn (integrand z) (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).mul_const C).mono'
  · exact ((Real.continuous_exp.comp continuous_neg).smul hz).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integrand, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hbound t ht.le) (Real.exp_pos _).le

def integral (z : ℝ → G) : G := ∫ t : ℝ in Ioi 0, integrand z t

omit [CompleteSpace H] in
theorem weak_equation (J : G →L[ℝ] H) (z : ℝ → G) (hz : Continuous z)
    (C : ℝ) (hbound : ∀ t, 0 ≤ t → ‖z t‖ ≤ C)
    (hevolve : ∀ v : G, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => inner ℝ (J (z s)) (J v))
        (-(inner ℝ (z t) v - inner ℝ (J (z t)) (J v))) t)
    (v : G) : inner ℝ (integral z) v = inner ℝ (J (z 0)) (J v) := by
  let ψ : ℝ → ℝ := fun t => Real.exp (-t) * inner ℝ (J (z t)) (J v)
  let ψ' : ℝ → ℝ := fun t => -Real.exp (-t) * inner ℝ (z t) v
  have hψ : Continuous ψ := (Real.continuous_exp.comp continuous_neg).mul
    ((J.continuous.comp hz).inner continuous_const)
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt ψ (ψ' t) t := by
    have hdexp := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    apply (hdexp.mul (hevolve v t ht)).congr_deriv
    dsimp [ψ']
    ring
  have hi := integrand_integrable z hz C hbound
  have hiψ' : IntegrableOn ψ' (Ioi 0) := by
    apply (((innerSL ℝ v).integrable_comp hi).neg).congr
    exact ae_of_all _ (fun t => by
      change -inner ℝ v (Real.exp (-t) • z t) = _
      rw [real_inner_smul_right]
      dsimp [ψ']
      rw [real_inner_comm v (z t)]
      ring)
  have hbψ : IsBoundedUnder (· ≤ ·) atTop ((fun t => ‖inner ℝ (J (z t)) (J v)‖)) := by
    apply isBoundedUnder_of_eventually_le
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    calc
      _ ≤ ‖J (z t)‖ * ‖J v‖ := norm_inner_le_norm _ _
      _ ≤ (‖J‖ * C) * ‖J v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (J.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg J))
  have htendsto : Tendsto ψ atTop (𝓝 0) :=
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).zero_mul_isBoundedUnder_le hbψ
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hψ.continuousWithinAt
    (fun t ht => hderiv t ht) hiψ' htendsto
  have hin : (∫ t : ℝ in Ioi 0, ψ' t) = -inner ℝ (integral z) v := by
    have heq : ψ' = fun t => -inner ℝ v (integrand z t) := by
      funext t
      dsimp [ψ', integrand]
      rw [real_inner_smul_right, real_inner_comm v (z t)]
      ring
    rw [heq, integral_neg]
    have heinner := (innerSL ℝ v).integral_comp_comm hi
    change (∫ t : ℝ in Ioi 0, inner ℝ v (integrand z t)) = inner ℝ v (integral z) at heinner
    rw [heinner]
    exact congrArg Neg.neg (real_inner_comm v (integral z)).symm
  rw [hin] at hFTC
  simpa only [ψ, neg_zero, Real.exp_zero, one_mul, zero_sub, neg_inj] using hFTC

theorem integral_eq_adjoint (J : G →L[ℝ] H) (z : ℝ → G) (hz : Continuous z)
    (C : ℝ) (hbound : ∀ t, 0 ≤ t → ‖z t‖ ≤ C)
    (hevolve : ∀ v : G, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => inner ℝ (J (z s)) (J v))
        (-(inner ℝ (z t) v - inner ℝ (J (z t)) (J v))) t) :
    integral z = J.adjoint (J (z 0)) := by
  apply ext_inner_right ℝ
  intro v
  rw [weak_equation J z hz C hbound hevolve v, J.adjoint_inner_left]

theorem image_integral_eq_resolvent (J : G →L[ℝ] H) (z : ℝ → G) (hz : Continuous z)
    (C : ℝ) (hbound : ∀ t, 0 ≤ t → ‖z t‖ ≤ C)
    (hevolve : ∀ v : G, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => inner ℝ (J (z s)) (J v))
        (-(inner ℝ (z t) v - inner ℝ (J (z t)) (J v))) t) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) • J (z t)) = (J.comp J.adjoint) (J (z 0)) := by
  have hi := integrand_integrable z hz C hbound
  calc
    _ = J (integral z) := by
      change (∫ t : ℝ in Ioi 0, Real.exp (-t) • J (z t)) = J (∫ t : ℝ in Ioi 0, integrand z t)
      rw [← J.integral_comp_comm hi]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        change Real.exp (-t) • J (z t) = J (Real.exp (-t) • z t)
        exact (J.map_smul _ _).symm)
    _ = _ := by rw [integral_eq_adjoint J z hz C hbound hevolve]; rfl

end
end SlowEquilibration.GraphLaplace
