-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSCovarianceDirectionalDerivative
public import SlowEquilibration.SphericalTAPCertificate

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSFiniteMixtureDirectionalDerivative

open Set Filter MeasureTheory CrisantiSommers CSCompactAttainment
open CSCovarianceDirectionalDerivative CSGeneralCovarianceStability
open CSParisiMeasure SphericalTAPCertificate
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

def perturbationLipschitzConstant (μ : FiniteMixture) (k : ℕ) : ℝ≥0 :=
  mixtureLipschitzConstant μ + k

/-- A coefficient perturbation by `t r^k`, with `|t|≤1`, has a single
Lipschitz bound uniform in `t`, including the unperturbed covariance. -/
theorem monomial_perturbation_lipschitzOn (μ : FiniteMixture) (k : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) :
    LipschitzOnWith (perturbationLipschitzConstant μ k)
      (fun r => μ.xi r+t*r^k) (Icc (0 : ℝ) 1) := by
  have hm : LipschitzOnWith (k : ℝ≥0)
      (fun r : ℝ => t*r^k) (Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun r _ => ((hasDerivAt_pow k r).const_mul t).differentiableAt) ?_
      (convex_Icc 0 1)
    intro r hr
    apply NNReal.coe_le_coe.mp
    change ‖deriv (fun r : ℝ => t*r^k) r‖ ≤ (k : ℝ)
    rw [((hasDerivAt_pow k r).const_mul t).deriv, Real.norm_eq_abs]
    have hp : 0 ≤ r^(k-1) := pow_nonneg hr.1 _
    have hp1 : r^(k-1) ≤ 1 := pow_le_one₀ hr.1 hr.2
    calc
      |t * ((k : ℝ) * r^(k-1))| = |t| * (k : ℝ) * r^(k-1) := by
        simp only [abs_mul, abs_of_nonneg (show 0 ≤ (k : ℝ) from Nat.cast_nonneg k),
          abs_of_nonneg hp]
        ring
      _ ≤ 1 * (k : ℝ) * 1 := by gcongr
      _ = (k : ℝ) := by ring
  simpa only [perturbationLipschitzConstant] using
    (mixture_xi_lipschitzOn μ).add hm

theorem base_lipschitzOn (μ : FiniteMixture) (k : ℕ) :
    LipschitzOnWith (perturbationLipschitzConstant μ k)
      μ.xi (Icc (0 : ℝ) 1) :=
  (mixture_xi_lipschitzOn μ).weaken (by
    simp only [perturbationLipschitzConstant]
    exact le_add_of_nonneg_right (by positivity))

/-- The ordinary finite-mixture CS optimum differentiates under a pure
covariance perturbation. This is entirely variational; a physical moment
identity still requires the corresponding finite-pressure response and the
thermodynamic pressure formula for the perturbed mixture. -/
theorem hasDerivAt_finiteMixture_monomial_value
    (μ : FiniteMixture) (β : ℝ) (k : ℕ) :
    HasDerivAt
      (fun t =>
        (locallyPerturbedMinimizer β μ.xi k
          (perturbationLipschitzConstant μ k)
          (base_lipschitzOn μ k)
          (fun s hs => monomial_perturbation_lipschitzOn μ k
            (abs_le.mpr ⟨by linarith [hs.1],hs.2.le⟩)) t).value β
          (fun r => μ.xi r+t*r^k))
      ((β^2/2)*(1-∫ r, r^k ∂(canonicalMinimizer μ β).law)) 0 := by
  have hd := hasDerivAt_actual_monomial_covariance_minimum β μ.xi k
    (perturbationLipschitzConstant μ k) (base_lipschitzOn μ k)
    (fun s hs => monomial_perturbation_lipschitzOn μ k
      (abs_le.mpr ⟨by linarith [hs.1],hs.2.le⟩))
  convert hd using 1
  have hzero :
      (locallyPerturbedMinimizer β μ.xi k
        (perturbationLipschitzConstant μ k)
        (base_lipschitzOn μ k)
        (fun s hs => monomial_perturbation_lipschitzOn μ k
          (abs_le.mpr ⟨by linarith [hs.1],hs.2.le⟩)) 0).law =
        (canonicalMinimizer μ β).law := by
    have hmin := lipschitzMinimizer_isMinimizer β (fun r => μ.xi r+0*r^k)
      (perturbationLipschitzConstant μ k)
      (monomial_perturbation_lipschitzOn μ k (by norm_num))
    have heq := eq_canonicalMinimizer_of_isMinimizer μ β _ (by
      simpa only [zero_mul, add_zero] using hmin)
    simp only [locallyPerturbedMinimizer]
    split_ifs with ht
    · simpa only [zero_mul, add_zero] using congrArg Admissible.law heq
    · norm_num at ht
  rw [hzero]

/-- In the source one-step phase, the covariance-direction derivative is
the overlap moment predicted by its actual two-atom CS minimizer. -/
theorem certificate_monomial_value_derivative
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (k : ℕ) (hk : 0 < k) :
    deriv
      (fun t =>
        (locallyPerturbedMinimizer β μ.xi k
          (perturbationLipschitzConstant μ k)
          (base_lipschitzOn μ k)
          (fun s hs => monomial_perturbation_lipschitzOn μ k
            (abs_le.mpr ⟨by linarith [hs.1],hs.2.le⟩)) t).value β
          (fun r => μ.xi r+t*r^k)) 0 =
      (β^2/2)*(1-(1-x)*Q^k) := by
  rw [(hasDerivAt_finiteMixture_monomial_value μ β k).deriv]
  rw [h.canonical_law, integral_twoAtom
    ⟨h.weight_range.1.le,h.weight_range.2.le⟩]
  simp [Nat.ne_of_gt hk]

end SlowEquilibration.CSFiniteMixtureDirectionalDerivative
