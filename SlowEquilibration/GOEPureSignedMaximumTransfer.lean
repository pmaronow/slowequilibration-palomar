-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEPhysicalSignedMean
public import SlowEquilibration.GOEMaximumRelativeLoss
public import SlowEquilibration.PosteriorMaximumDeterminant

/-! The signed physical GOE determinant and the actual local-maximum
determinant agree on every negative-Hessian sample. Their expectations differ
only by the actual exponentially rare nonmaximum contribution. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEPureSignedMaximumTransfer
open Set MeasureTheory ProbabilityTheory Filter
open GOEAsymptotics GOEClippedDeterminants GOEExtremalEdges
open GOEMaximumDeterminant GOERawMoments GOEPhysicalSignedMean
open GOEPhysicalPotential
open UnrestrictedConditionedDeterminants SphericalMarkedWindows
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- On a symmetric matrix below the shift, its shifted determinant is strictly
positive, so the maximum weight is the signed characteristic polynomial. -/
theorem shifted_determinant_pos_of_maximumEvent (n : ℕ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hW : ∀ i j, W i j = W j i) {k : ℝ}
    (hk : W ∈ maximumEvent n k) : 0 < (k • 1-W).det := by
  have hSym : ∀ i j, matrixToGaussian W i j = matrixToGaussian W j i := hW
  have hProd : (k • 1-W).det = ∏ i : Fin (n+1), (k-eigenvalues n W i) := by
    simpa only [gaussianToMatrix_matrixToGaussian, eigenvalues] using
      (shifted_det_eq_prod k (matrixToGaussian W) hSym)
  rw [hProd]
  apply Finset.prod_pos
  intro i hi
  have htop : eigenvalues n W 0 < k := hk
  exact sub_pos.mpr ((eigenvalues_antitone n W (Fin.zero_le i)).trans_lt htop)

/-- Every discrepancy between the actual signed and maximum means is paid
for by the ordinary absolute determinant on the excluded event. -/
theorem signedPhysicalMean_sub_maximumMean_abs_le_excluded
    (n N : ℕ) (b k : ℝ) :
    |signedPhysicalMean (n+1) N b k-maximumMean n N b k| ≤
      ∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
        ∂SphericalGaussianJet.goeLaw (n+1) N b := by
  let ν := SphericalGaussianJet.goeLaw (n+1) N b
  let f := fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => (k • 1-W).det
  have hfn (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
      f W = (-1:ℝ)^(n+1)*(W-k • 1).det := by
    dsimp only [f]
    rw [show k • 1-W = -(W-k • 1) by abel, Matrix.det_neg]
    simp
  have hInt : Integrable f ν := by
    change Integrable (fun W => f W) ν
    simp only [hfn]
    exact (fixed_shifted_determinant_integrable (n+1) N b k).const_mul _
  have hEvent := maximumEvent_measurable n k
  have hGood : (∫ W in maximumEvent n k, f W ∂ν) = maximumMean n N b k := by
    unfold maximumMean
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (SphericalMarkedWindows.goe_symmetric_ae (n+1) N b),
      ae_restrict_mem hEvent] with W hW hMem
    change f W = |f W|
    exact (abs_of_pos (shifted_determinant_pos_of_maximumEvent n W hW hMem)).symm
  have hSplit := integral_add_compl hEvent hInt
  have hDiff : signedPhysicalMean (n+1) N b k-maximumMean n N b k =
      ∫ W in (maximumEvent n k)ᶜ, f W ∂ν := by
    change (∫ W, f W ∂ν)-maximumMean n N b k = _
    rw [← hSplit, hGood]
    ring
  rw [hDiff]
  change |∫ W in (maximumEvent n k)ᶜ, f W ∂ν| ≤
    ∫ W in (maximumEvent n k)ᶜ, |f W| ∂ν
  exact abs_integral_le_integral_abs

/-- Uniform exponentially small relative discrepancy between the two
genuine physical GOE means on each fixed exterior compact interval. -/
theorem signedPhysicalMean_maximumMean_relative_loss {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      |signedPhysicalMean (n+1) (n+2) b k-maximumMean n (n+2) b k| ≤
        C*Real.exp (-c*(n+2:ℕ))*maximumMean n (n+2) b k := by
  obtain ⟨C,c,hC,hc,hLoss⟩ := excluded_determinant_relative_loss (Z:=Z) hb hg
  refine ⟨2*C,c,by positivity,hc,?_⟩
  filter_upwards [hLoss, maximumMean_comparison_eventually (Z:=Z) hb hg]
    with n hLossN hHalf
  intro k hk
  calc
    _ ≤ ∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
          ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b :=
      signedPhysicalMean_sub_maximumMean_abs_le_excluded n (n+2) b k
    _ ≤ C*Real.exp (-c*(n+2:ℕ))*physicalMean n (n+2) b k := hLossN k hk
    _ ≤ (2*C)*Real.exp (-c*(n+2:ℕ))*maximumMean n (n+2) b k := by
      have hh := (hHalf k hk).1
      have hmul := mul_le_mul_of_nonneg_left hh
        (by positivity : 0 ≤ 2*C*Real.exp (-c*(n+2:ℕ)))
      nlinarith

end SlowEquilibration.GOEPureSignedMaximumTransfer
