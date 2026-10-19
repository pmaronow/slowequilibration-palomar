-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalSingleWitnessTightness

/-! A deterministic growing physical energy window for source 11.14.
Monotonicity of the joint event converts the dimension-then-window limit
into an ordinary probability limit along any diverging window radius. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The monotone diagonal step needs no quantitative rate in the fixed
window limit. -/
theorem source_monotone_diagonal_of_liminf_tendsto_one
    (p : ℕ → ℝ → ℝ) (w : ℕ → ℝ)
    (hmono : ∀ n, Monotone (p n))
    (hlo : ∀ n t, 0 ≤ p n t) (hhi : ∀ n t, p n t ≤ 1)
    (hp : Tendsto (fun t => Filter.liminf (fun n => p n t) atTop) atTop (𝓝 1))
    (hw : Tendsto w atTop atTop) :
    Tendsto (fun n => p n (w n)) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let b := (a+1)/2
    have hab : a < b := by dsimp [b]; linarith
    have hb : b < (1:ℝ) := by dsimp [b]; linarith
    have hlarge : ∀ᶠ t in atTop,
        b < Filter.liminf (fun n => p n t) atTop :=
      (tendsto_order.1 hp).1 b hb
    obtain ⟨t,ht⟩ := hlarge.exists
    have hBound : IsBoundedUnder (· ≥ ·) atTop (fun n => p n t) :=
      isBoundedUnder_of ⟨0,fun n => hlo n t⟩
    have hevent := eventually_lt_of_lt_liminf ht hBound
    filter_upwards [hevent,hw.eventually_gt_atTop t] with n hn hnt
    exact (hab.trans hn).trans_le (hmono n hnt.le)
  · intro b hb
    exact Eventually.of_forall (fun n => (hhi n (w n)).trans_lt hb)

/-- The ordinary critical-point joint event increases with the physical
window radius, including its upper bound on the global maximum. -/
theorem source_critical_joint_probability_monotone_window
    (n : ℕ) (μ : FiniteMixture) (Q L R m : ℝ) :
    Monotone (fun t : ℝ => (disorderLaw (n+3) μ.maxDegree).real
      {J | (sourceCriticalPhysicalWindowSet n μ Q
        (m-t) (m+t) (Ioo L R) J).Nonempty ∧
        sourceSphereMaximum (n+1) μ Q J < m+t}) := by
  intro t s hts
  apply measureReal_mono
  · intro J hJ
    refine ⟨?_,by linarith [hJ.2]⟩
    obtain ⟨u,hu⟩ := hJ.1
    refine ⟨u,?_⟩
    change (‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈ Icc (m-t) (m+t) ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R) at hu
    change (‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈ Icc (m-s) (m+s) ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R)
    exact ⟨hu.1,hu.2.1,⟨by linarith [hu.2.2.1.1],by linarith [hu.2.2.1.2]⟩,
      hu.2.2.2⟩
  · finiteness

/-- The source 11.14 joint event has probability tending to one when the
physical energy half-width is `sqrt (n+3)`. The same conclusion holds for
every half-width tending to infinity. The radial interval and center come
from the unconditional 11.13--11.14 single-witness package. -/
theorem source_mixed_actual_canonical_growing_window_existence
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    ∃ L R : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ w : ℕ → ℝ, Tendsto w atTop atTop →
          Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
            {J | (sourceCriticalPhysicalWindowSet n μ Q
              (d.center (n+1)-w n) (d.center (n+1)+w n) (Ioo L R) J).Nonempty ∧
              sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+w n})
            atTop (𝓝 1) := by
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments,hProb,hMax,hCard,hGround⟩ :=
    source_mixed_actual_canonical_single_witness_with_maximum_tightness
      μ h hnp hd hδMax
  refine ⟨L,R,hL,hR,hEdge,d,?_⟩
  intro w hw
  let p (n : ℕ) (t : ℝ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceCriticalPhysicalWindowSet n μ Q
      (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
      sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}
  have hp : Tendsto (fun t => Filter.liminf (fun n => p n t) atTop)
      atTop (𝓝 1) := by simpa only [p] using hGround
  have hlim := source_monotone_diagonal_of_liminf_tendsto_one p w
    (fun n => source_critical_joint_probability_monotone_window n μ Q L R (d.center (n+1)))
    (fun n t => measureReal_nonneg) (fun n t => measureReal_le_one) hp hw
  simpa only [p] using hlim

/-- An explicit growing width on the original physical energy scale. -/
theorem source_mixed_actual_canonical_sqrt_window_existence
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    ∃ L R : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | (sourceCriticalPhysicalWindowSet n μ Q
            (d.center (n+1)-Real.sqrt (n+3:ℕ))
            (d.center (n+1)+Real.sqrt (n+3:ℕ)) (Ioo L R) J).Nonempty ∧
            sourceSphereMaximum (n+1) μ Q J <
              d.center (n+1)+Real.sqrt (n+3:ℕ)}) atTop (𝓝 1) := by
  obtain ⟨L,R,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_canonical_growing_window_existence μ h hnp hd hδMax
  refine ⟨L,R,hL,hR,hEdge,d,?_⟩
  have hdim : Tendsto (fun n : ℕ => ((n+3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  exact hall (fun n => Real.sqrt (n+3:ℕ)) (Real.tendsto_sqrt_atTop.comp hdim)

end
end SlowEquilibration.PairConditionalDeterminantMoments
