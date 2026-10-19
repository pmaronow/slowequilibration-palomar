-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalPrefactors
public import SlowEquilibration.GOESharpMoments

/-! # Genuine all-dimension canonical physical determinant normalization

The exact lower prefactor and genuine moment prefactors yield the source's
ordinary normalized moments in every positive matrix dimension at fixed
codimension. The sharp eventual bound is retained from actual concentration.
-/

@[expose] public section

namespace SlowEquilibration.GOEPhysicalNormalizedMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEScaling GOERawMoments GOEPrefactors GOEPhysicalPotential GOEPhysicalPrefactors
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact lower ordinary prefactor for every physical positive dimension. -/
theorem physicalMean_lower (n j : ℕ) {b k : ℝ} (hb : 0 < b)
    (hk : 2 * Real.sqrt b < k) :
    Real.exp (physicalRate n j b k) ≤ physicalMean n (n + 1 + j) b k := by
  have hN : 0 < n + 1 + j := by omega
  have ha := scaleFactor_pos n hN hb
  have hstd : 2 < k / scaleFactor n (n + 1 + j) b := by
    apply (lt_div_iff₀ ha).mpr
    exact (mul_le_mul_of_nonneg_left (scaleFactor_le_sqrt hN (by omega) hb.le)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hk
  rw [exp_rate_factor n j hb k, physicalMean_scaling n hN hb]
  exact mul_le_mul_of_nonneg_left (meanAbsolute_lower n hstd) (pow_pos ha _).le

/-- Actual own expectation positivity, proved without a target mean premise. -/
theorem physicalMean_pos (n j : ℕ) {b k : ℝ} (hb : 0 < b)
    (hk : 2 * Real.sqrt b < k) : 0 < physicalMean n (n + 1 + j) b k :=
  (Real.exp_pos _).trans_le (physicalMean_lower n j hb hk)

/-- The source canonical normalized moment conclusion in every positive
matrix dimension, with its own literal ordinary expectation. -/
theorem normalized_physical_moments (j : ℕ) {b g Z r : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k → k ≤ Z →
      Integrable (matrixAbsoluteDet n k)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ∧
      0 < physicalMean n (n + 1 + j) b k ∧
      Integrable (fun W => (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ∧
      (∫ W, (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r
        ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ≤ C := by
  obtain ⟨C, hC, hmoment⟩ := physical_moments_prefactors j (Z := Z) hb hg hr
  obtain ⟨C1, hC1, hfirst⟩ := physical_moments_prefactors j (Z := Z) hb hg (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  intro n k hk hZ
  have hkedge : 2 * Real.sqrt b < k := by linarith
  have hmean := physicalMean_pos n j hb hkedge
  have hraw := hmoment n k hk hZ
  have hD : Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) := by
    simpa only [Real.rpow_one] using (hfirst n k hk hZ).1
  have hratio (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r =
        matrixAbsoluteDet n k W ^ r / (physicalMean n (n + 1 + j) b k) ^ r :=
    Real.div_rpow (show 0 ≤ matrixAbsoluteDet n k W from abs_nonneg _) hmean.le r
  have hint : Integrable (fun W => (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r)
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) := by
    simpa only [hratio] using hraw.1.div_const ((physicalMean n (n + 1 + j) b k) ^ r)
  refine ⟨hD, hmean, hint, ?_⟩
  simp only [hratio]
  rw [integral_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hmean r)).mpr
  have hden := Real.rpow_le_rpow (Real.exp_pos _).le (physicalMean_lower n j hb hkedge) hr
  rw [← Real.exp_mul] at hden
  have hden' : Real.exp (r * physicalRate n j b k) ≤ (physicalMean n (n + 1 + j) b k) ^ r := by
    simpa only [mul_comm (physicalRate n j b k) r] using hden
  exact hraw.2.trans (mul_le_mul_of_nonneg_left hden' hC.le)

/-- Sharp normalized canonical bounds in the same genuine physical law,
for every fixed codimension and all sufficiently large matrix dimensions. -/
theorem normalized_physical_moments_sharp_eventually (j : ℕ) {b g : ℝ}
    (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun W => (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ∧
      (∫ W, (matrixAbsoluteDet n k W / physicalMean n (n + 1 + j) b k) ^ r
        ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ≤
          (2 : ℝ) ^ r * Real.exp (4 * b * r ^ 2 / g ^ 2) := by
  filter_upwards [GOESharpMoments.goe_determinant_moments_eventually hb hg] with n hn
  intro k hk r hr
  have h := (hn (n + 1 + j) (by omega) k hk).2.2 r hr
  simpa only [physicalMean, GOESharpMoments.matrixAbsoluteDet, GOERawMoments.matrixAbsoluteDet] using h

end
end SlowEquilibration.GOEPhysicalNormalizedMoments
