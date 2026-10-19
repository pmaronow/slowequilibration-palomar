-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedCenterFirstMoment

/-! Source 11.14 uniform-in-dimension expected count for all critical
points in each fixed centered proper-pure value and radial-mark window. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open TwoAtomStationarity SphericalTAPCertificate
open scoped ENNReal Topology
set_option autoImplicit false

theorem source_pure_actual_critical_center_count_uniform
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∃ m : ℕ → ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L) ≤ B) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  obtain ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hC,hcut,hη,hε,hC₂,hD,
    hFallback,hCenter,hUnfiltered,hMean,hMoments⟩ :=
    source_pure_actual_retained_center_first_moment p hp a ha h
  refine ⟨m,δ,hδ,hUnfiltered,?_⟩
  intro L hL
  obtain ⟨B,hB⟩ := (hUnfiltered (-L) L (by linarith)).bddAbove_range
  refine ⟨B,?_⟩
  intro n
  constructor
  · exact sourceUnfilteredValueWindowCount_lintegral_lt_top (n+2) (by omega)
      μ h.overlap_range.1 (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
  · exact hB (mem_range_self n)

end SlowEquilibration.PairConditionalDeterminantMoments
