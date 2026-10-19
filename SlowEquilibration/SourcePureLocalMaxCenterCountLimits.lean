-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxWindowCountBridge

/-! Source proper-pure centering and exact first-moment limits for the
ordinary count of local maxima in every fixed physical-energy window,
with the compatible radial mark interval imposed exactly. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_truncatedLocalMax_center_count_limits
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M : ℝ, 0 < M ∧
      (∀ n < n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n ≥ n₀, tail (f n) (m n)=1 ∧
        (∀ y : ℝ, tail (f n) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (m n+L) (m n+R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) := by
  obtain ⟨n₀,m,M,hM,hFallback,hCenter,hDensity,hTail⟩ :=
    sourcePure_truncatedLocalMax_center_and_limits p hp a ha h hm hg hLeft hRight
  refine ⟨n₀,m,M,hM,hFallback,hCenter,?_⟩
  intro L R hLR
  have hi : ∀ᶠ n : ℕ in atTop, Integrable
      (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) :=
    pureTruncatedLocalMaxDensity_integrable_eventually
      p hp a ha h (hm.1.trans hm.2) hg hLeft hRight
  have hWindow := compact_centered_window_integral_limit m hi hTail hLR
  have he : (fun n : ℕ => ∫ H in Icc (m n+L) (m n+R),
      pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H) =ᶠ[atTop]
      (fun n : ℕ => sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r
        (m n+L) (m n+R)) :=
    Filter.Eventually.of_forall (fun n =>
      (sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
        h.overlap_range.1 l r (m n+L) (m n+R)).symm)
  exact hWindow.congr' he

end SlowEquilibration.SphericalMarkedWindows
