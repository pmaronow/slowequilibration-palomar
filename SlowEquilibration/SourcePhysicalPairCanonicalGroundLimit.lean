-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalGroundTightness

/-! The iterated fixed-window limit in source 11.14. Dimension tends to
infinity first. Only afterward does the fixed window radius tend to
infinity; no growing-window assertion is introduced. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem source_canonical_ground_error_tendsto_zero (c k : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.exp (-c*t)+
      k/(Real.exp (c*t)-Real.exp (-c*t))) atTop (𝓝 0) := by
  have hPos : Tendsto (fun t : ℝ => Real.exp (c*t)) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop hc)
  have hNeg : Tendsto (fun t : ℝ => Real.exp (-c*t)) atTop (𝓝 (0:ℝ)) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hDen : Tendsto (fun t : ℝ => Real.exp (c*t)-Real.exp (-c*t))
      atTop atTop := by
    simpa only [sub_eq_add_neg] using hPos.atTop_add hNeg.neg
  have hFrac : Tendsto (fun t : ℝ => k/(Real.exp (c*t)-Real.exp (-c*t)))
      atTop (𝓝 (0:ℝ)) := hDen.const_div_atTop k
  simpa only [zero_add] using hNeg.add hFrac

/-- The source 11.14 iterated ground-event limit, with an ordinary set of
mixed-model critical points and original-disorder probabilities. The
centering and radial interval are constructed from the certificate. -/
theorem source_mixed_actual_canonical_joint_ground_iterated_limit
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    ∃ L R : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        Tendsto (fun t : ℝ => Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | (Set.Nonempty {u : Vector (n+3) |
              ‖u‖^2=(n+3:ℕ) ∧
              surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
              field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
                Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
              actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R}) ∧
              sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop)
          atTop (𝓝 1) := by
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_canonical_joint_ground_probability μ h hnp hd hδMax
  obtain ⟨D,_hD,hfixed⟩ := hall (α := (3:ℝ)/8) (by norm_num) (by norm_num)
  refine ⟨L,R,hL,hR,hEdge,d,?_⟩
  let k := 1+(1-ε)/(cut^2-ε)
  let p (t : ℝ) := Filter.liminf (fun n : ℕ =>
    (disorderLaw (n+3) μ.maxDegree).real
      {J | (Set.Nonempty {u : Vector (n+3) |
        ‖u‖^2=(n+3:ℕ) ∧
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
        field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
          Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R}) ∧
        sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hLower : Tendsto (fun t : ℝ =>
      1-(Real.exp (-(β*x)*t)+k/
        (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)))) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (source_canonical_ground_error_tendsto_zero
        (β*x) k hc0) : Tendsto (fun t : ℝ =>
        (1:ℝ)-(Real.exp (-(β*x)*t)+k/
          (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)))) atTop (𝓝 (1-0)))
  have hUpper : ∀ t : ℝ, p t ≤ 1 := by
    intro t
    have hBound : IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (Set.Nonempty {u : Vector (n+3) |
          ‖u‖^2=(n+3:ℕ) ∧
          surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
          field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
            Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
          actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R}) ∧
          sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) :=
      isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
    apply Filter.liminf_le_of_le hBound
    intro b hb
    obtain ⟨n,hn⟩ := hb.exists
    exact hn.trans measureReal_le_one
  have hResult : Tendsto p atTop (𝓝 1) := by
    apply hLower.squeeze' tendsto_const_nhds
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      simpa only [p,k] using hfixed t ht
    · exact Eventually.of_forall hUpper
  simpa only [p] using hResult

end
end SlowEquilibration.PairConditionalDeterminantMoments
