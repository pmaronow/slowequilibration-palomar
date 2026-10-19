-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalSingleWitness

/-! The global-maximum tightness consequence for the exact same source
11.13--11.14 center and retained-point filter. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- One common choice of center, radial interval and selection parameters
supports the exact 11.13 moments, 11.14 count probabilities and ordinary
critical-point conclusions, as well as tightness of the original mixed
Hamiltonian maximum around that center. -/
theorem source_mixed_actual_canonical_single_witness_with_maximum_tightness
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ C cut η ε L R : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 hd ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss (g/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧ sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        (∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ a b : ℝ, a < b →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            let X n J := (sourceRetainedScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (g/2) C ε η E G J).toReal
            Tendsto aN atTop
              (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) ∧
              ∀ᶠ n : ℕ in atTop,
                (∫ J, (X n J)^2 ∂disorderLaw (n+3) μ.maxDegree) ≤
                  (1+D*sourcePrintedPairError α n)*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                ProbabilityTheory.variance (X n)
                  (disorderLaw (n+3) μ.maxDegree) ≤
                  D*sourcePrintedPairError α n*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree)) ∧
        (∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ t : ℝ, 0 < t →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)-t) (d.center (n+1)+t)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            let X n J := (sourceRetainedScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (g/2) C ε η E G J).toReal
            Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
              {J | X n J = 0}) atTop ≤
              (1+(1-ε)/(cut^2-ε)) /
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)) ∧
            Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
              {J | X n J < aN n/2}) atTop ≤
              4*(1+(1-ε)/(cut^2-ε)) /
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))) ∧
        (∀ t : ℝ, 0 < t →
          Filter.limsup (fun n : ℕ =>
            (disorderLaw (n+3) μ.maxDegree).real
              {J | |sourceSphereMaximum (n+1) μ Q J-d.center (n+1)| > t}) atTop ≤
            Real.exp (-(β*x)*t)+
              (1+(1-ε)/(cut^2-ε)) /
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))) ∧
        (∀ t : ℝ, 0 < t →
          ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
            sourceCriticalPhysicalWindowCardMean n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) ≤ B) ∧
        Tendsto (fun t : ℝ => Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | (sourceCriticalPhysicalWindowSet n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
              sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop)
          atTop (𝓝 1) := by
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments,hProb,hCard,hGround⟩ :=
    source_mixed_actual_canonical_single_witness_11_13_11_14 μ h hnp hd hδMax
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments,hProb,?_,hCard,hGround⟩
  obtain ⟨D,_hD,hwin⟩ := hProb (α := (3:ℝ)/8) (by norm_num) (by norm_num)
  have hm : markK μ β Q ∈ Ioo L R := ⟨hL,hR⟩
  have hκ : 0 < sourceMarkedLeastCurvature μ Q :=
    sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by omega) hnp
  have hu : 0 < sourceRadialClearance μ β Q (Ioo L R) :=
    sourceRadialClearance_pos μ hm
  let δ := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  have hδ : 0 < δ := by
    dsimp [δ]
    have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    positivity
  intro t ht
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let a := (1+(1-ε)/(cut^2-ε)) /
    (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))
  have hZero := (hwin t ht).1
  have hUpper := sourceSphereMaximum_centered_probability_limsup_shift
    μ h hnp hEdge hm hδ (le_refl _) d t
  have hTight := source_retained_window_maximum_tightness_of_limsup
    μ Q (fun n => d.center (n+1)) (Ioo L R)
    (g/2) C ε η E G t a (Real.exp (-(β*x)*t)) hZero hUpper
  simpa only [a,G,E,g] using hTight

end
end SlowEquilibration.PairConditionalDeterminantMoments
