-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEPureSignedMaximumTransfer
public import SlowEquilibration.GOEMaximumRelativeLoss

/-! The ordinary absolute GOE determinant mean in the proper-pure one-point
intensity differs from the signed Hermite mean only on the genuine excluded
nonmaximum event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEPureSignedMaximumTransfer
open Set MeasureTheory ProbabilityTheory Filter
open GOEMaximumDeterminant GOEPhysicalPotential GOEPhysicalSignedMean
open GOERawMoments
open scoped Topology
set_option maxHeartbeats 500000

/-- Uniform exponential relative agreement of the actual ordinary absolute
GOE mean and signed physical Hermite mean on each fixed exterior compact
interval. This is an estimate on true expectations, with no determinant
comparison hypothesis. -/
theorem signedPhysicalMean_absoluteMean_relative_loss {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      |physicalMean n (n+2) b k-signedPhysicalMean (n+1) (n+2) b k| ≤
        C*Real.exp (-c*(n+2 : ℕ))*physicalMean n (n+2) b k := by
  obtain ⟨C,c,hC,hc,hLoss⟩ := excluded_determinant_relative_loss (Z := Z) hb hg
  refine ⟨2*C,c,by positivity,hc,?_⟩
  filter_upwards [hLoss,goe_determinant_moments_eventually hb hg] with n hn hMom
  intro k hk
  let excluded := ∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
    ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b
  have hInt : Integrable (matrixAbsoluteDet n k)
      (SphericalGaussianJet.goeLaw (n+1) (n+2) b) := by
    exact (hMom (n+2) (by omega) k hk.1).1
  have hSplit := integral_add_compl (maximumEvent_measurable n k) hInt
  have hDecomp : physicalMean n (n+2) b k = maximumMean n (n+2) b k+excluded := by
    exact hSplit.symm
  have hExcNonneg : 0 ≤ excluded := integral_nonneg (fun _ => abs_nonneg _)
  have hSigned := signedPhysicalMean_sub_maximumMean_abs_le_excluded n (n+2) b k
  have hSigned' : |maximumMean n (n+2) b k-signedPhysicalMean (n+1) (n+2) b k| ≤
      excluded := by rwa [abs_sub_comm] at hSigned
  have hExBound := hn k hk
  have hTri : |physicalMean n (n+2) b k-signedPhysicalMean (n+1) (n+2) b k| ≤
      |physicalMean n (n+2) b k-maximumMean n (n+2) b k|+
        |maximumMean n (n+2) b k-signedPhysicalMean (n+1) (n+2) b k| :=
    abs_sub_le _ _ _
  rw [show physicalMean n (n+2) b k-maximumMean n (n+2) b k=excluded by linarith [hDecomp],
    abs_of_nonneg hExcNonneg] at hTri
  calc
    _ ≤ excluded+|maximumMean n (n+2) b k-signedPhysicalMean (n+1) (n+2) b k| := hTri
    _ ≤ 2*excluded := by linarith
    _ ≤ (2*C)*Real.exp (-c*(n+2 : ℕ))*physicalMean n (n+2) b k := by
      nlinarith [mul_le_mul_of_nonneg_left hExBound (by norm_num : (0 : ℝ) ≤ 2)]

end SlowEquilibration.GOEPureSignedMaximumTransfer
