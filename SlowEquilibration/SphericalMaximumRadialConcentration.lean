-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumEnergyDifferential

/-! Uniform Gaussian concentration of the actual determinant-weighted
radial probability distribution around its true nearby-energy saddle. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open RadialGaussianBounds RadialLaplaceBounds
open scoped Topology ENNReal
set_option maxHeartbeats 400000

/-- Source10.5(d), for the original raw determinant-weighted probability law,
with constants before all nearby energies and all nonnegative tail radii. -/
theorem sourceMaximumRadialLaw_gaussian_concentration (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ t : ℝ,0 ≤ t →
        (sourceMaximumRadialLaw n μ Q (Ioo L R) e).real {k : ℝ | t ≤ |k-sourceRadialSaddle μ Q e|} ≤
          C*Real.exp (-c*(n+2 : ℕ)*t^2) := by
  obtain ⟨c,C,hc,hC,hBounds⟩ := sourceSaddle_density_gaussian_bounds μ h hnp hL
  obtain ⟨l,u,hl,_hu,hNorm⟩ := sourceSaddle_radial_normalization μ h hnp hL hm hA4
  let a := sourceRadialCurvature μ Q/2
  have ha : 0 < a := half_pos (sourceRadialCurvature_pos μ h.overlap_range.1 hnp)
  refine ⟨C*Real.sqrt (Real.pi/(a/2))/l,a/2,by positivity,half_pos ha,?_⟩
  filter_upwards [hBounds,hNorm] with n hn hNrm
  intro e he t ht
  have hMem := sourceRadialSaddle_mem_of_clearance μ hm (hA4 e he)
  have hEnv := hn e hMem
  rw [sourceMaximumRadialLaw_eq_physical n μ h.overlap_range.1 hnp]
  exact NormalizedRadialMeasure.gaussian_concentration measurableSet_Ioo
    (sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm ((n+2 : ℕ)*e))
    (fun _ => ENNReal.toReal_nonneg) hl hC.le ha (by positivity : 0 < ((n+2 : ℕ) : ℝ))
    (hNrm e he).1 (fun k hk => (hEnv k hk).2) ht
end SlowEquilibration.SphericalMarkedWindows
