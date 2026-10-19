-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceMixedCriticalEntranceCPTransfer
public import SlowEquilibration.SourceMixedCriticalCenteredWindowCount
public import SlowEquilibration.SphericalCountRectangles

/-! The centered mixed-model source critical-point entrance transfer with
the actual logarithmic center and all-critical expected count inserted. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedCenteredCriticalEntranceTransfer
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate
open ConditionedDeterminantMoments
open SourceMixedCriticalEntranceCPTransfer
open SourceMixedCriticalCenteredWindowCount
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem source_mixed_centered_critical_entrance_cp_transfer_of_ordinary
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β x L R : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R)
    {g Z r c C M : ℝ} (hg : 0 < g) (hr : 1 < r)
    (hc : 0 < c) (hC : 0 ≤ C) (hM : 0 < M)
    (hL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ L) (hR : R ≤ Z)
    (psi : (n : ℕ) → Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ)
    (hpsi : ∀ n, Measurable fun z : Disorder (n+2) μ.maxDegree ×
      Vector (n+2) => psi n z.1 z.2)
    (hpsi01 : ∀ n J u, 0 ≤ psi n J u ∧ psi n J u ≤ 1)
    (hordinary : ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ physicalEnergyWindow (n+2)
        (Icc (d.center n-M) (d.center n+M)) (Ioo L R) →
        (∫ J, psi n J u ∂mixedLaw μ Q u hu z) ≤
          C*(((n+2 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
            ((n+2 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
            Real.exp (-c*((n+2 : ℕ) : ℝ))) :
    ∃ (B Cdet : ℝ), 0 < B ∧ 0 < Cdet ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+2)
            (Icc (d.center n-M) (d.center n+M)) (Ioo L R))
          (fun J u => ENNReal.ofReal (psi n J u)) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal ((Cdet^(1/r)*(2*C+1)^(1-1/r)*B)*
          (((n+2 : ℕ) : ℝ)^
            ((-(((μ.minDegree : ℝ)-2)/2))*(1-1/r)))) := by
  obtain ⟨B,hB,hCount⟩ :=
    original_mixed_centered_critical_window_count_bounded μ hQ d hM
  let K (n : ℕ) := physicalEnergyWindow (n+2)
    (Icc (d.center n-M) (d.center n+M)) (Ioo L R)
  have hK (n : ℕ) : MeasurableSet (K n) := by
    exact rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul _)) measurableSet_Ioo
  have hgap (n : ℕ) (z : EuclideanSpace ℝ (Fin 2))
      (hz : z ∈ K n) :
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z := by
    change ((n+2 : ℕ) : ℝ)*z 0 ∈ Icc (d.center n-M) (d.center n+M) ∧
      z 1 ∈ Ioo L R at hz
    exact ⟨hL.trans hz.2.1.le, hz.2.2.le.trans hR⟩
  have hCountEvent : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) (K n)
          (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal B := .of_forall hCount
  obtain ⟨Cdet,hCdet,hBound⟩ := actual_mixed_critical_entrance_cp_transfer
    μ hd hQ hnp hg hr hc hC hB.le K hK psi hpsi hpsi01 hgap
    hordinary hCountEvent
  exact ⟨B,Cdet,hB,hCdet,hBound⟩

end SlowEquilibration.SourceMixedCenteredCriticalEntranceTransfer
