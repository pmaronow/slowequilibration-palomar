-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSConvexity
public import SlowEquilibration.MixtureCurvature

@[expose] public section

namespace SlowEquilibration.NonconvexCertificate

open MeasureTheory Set CrisantiSommers
noncomputable section

def exampleCoefficients : ℕ →₀ ℝ := Finsupp.single 4 1+Finsupp.single 12 b

/-- The actual nonnegative degree-4/degree-12 covariance is a canonical
finite mixture with no omitted or artificial coefficients. -/
def exampleMixture : FiniteMixture where
  coeff := exampleCoefficients
  nonneg := by
    intro p
    have hb := b_pos.le
    simp only [exampleCoefficients,Finsupp.add_apply,Finsupp.single_apply]
    split_ifs <;> positivity
  zero_below_two := by
    intro p hp
    have h4 : p≠4 := by omega
    have h12 : p≠12 := by omega
    simp [exampleCoefficients,h4,h12]
  nonzero := by
    intro hz
    have h := congrArg (fun f : ℕ →₀ ℝ => f 4) hz
    norm_num [exampleCoefficients] at h

theorem exampleMixture_support : exampleMixture.coeff.support={4,12} := by
  ext p
  by_cases h4 : p=4
  · subst p
    simp [exampleMixture,exampleCoefficients]
  by_cases h12 : p=12
  · subst p
    simp [exampleMixture,exampleCoefficients,b_pos.ne']
  simp [exampleMixture,exampleCoefficients,Finsupp.mem_support_iff,h4,h12]

theorem exampleMixture_xi (r : ℝ) : exampleMixture.xi r=xi r := by
  unfold FiniteMixture.xi
  rw [exampleMixture_support]
  norm_num [exampleMixture,exampleCoefficients,xi]

theorem exampleMixture_minDegree : exampleMixture.minDegree=4 := by
  unfold FiniteMixture.minDegree
  apply le_antisymm
  · exact Finset.min'_le _ 4 (by rw [exampleMixture_support];simp)
  · apply Finset.le_min'
    intro p hp
    rw [exampleMixture_support] at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl <;> norm_num

theorem exampleLaw_unique_minimizer (ζ : Admissible)
    (hζ : ζ.IsMinimizer beta exampleMixture.xi) : ζ=exampleLaw := by
  have hxi : exampleMixture.xi=xi := funext exampleMixture_xi
  rw [hxi] at hζ
  exact ζ.minimizer_unique exampleLaw beta xi
    (continuous_iff_continuousAt.mpr (fun r => (xi_hasDerivAt r).continuousAt)).continuousOn
    hζ exampleLaw_minimizer

/-- The full actual variational/nonconvex example: canonical finite mixture,
unique literal one-step minimizer, exactly two contacts, a nondegenerate
positive contact, the quantitative contact margin and failure of convexity. -/
theorem thermal_example :
    exampleMixture.minDegree=4 ∧
    0<beta ∧
    x ∈ Ioo (0:ℝ) 1 ∧ Q ∈ Ioo (0:ℝ) 1 ∧
    exampleLaw.IsMinimizer beta exampleMixture.xi ∧
    (∀ ζ : Admissible,ζ.IsMinimizer beta exampleMixture.xi → ζ=exampleLaw) ∧
    (∀ r ∈ Ico (0:ℝ) 1,V r=0 ↔ r=0 ∨ r=Q) ∧
    0<deriv (deriv V) Q ∧
    beta^2*(1-Q)^2*deriv (deriv exampleMixture.xi) Q<2/3 ∧
    ¬ConvexOn ℝ (Ioc (0:ℝ) 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv exampleMixture.xi))) := by
  have hxi : exampleMixture.xi=xi := funext exampleMixture_xi
  refine ⟨exampleMixture_minDegree,beta_pos,parameters_mem.1,parameters_mem.2,
    ?_,exampleLaw_unique_minimizer,actual_contact_set,
    strict_one_step_certificate.2.2.2,?_,?_⟩
  · rw [hxi]
    exact exampleLaw_minimizer
  · rw [hxi]
    exact actual_contact_margin
  · rw [hxi]
    exact inverse_not_convex

end
end SlowEquilibration.NonconvexCertificate
