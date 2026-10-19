-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceBandShrink
public import SlowEquilibration.SphericalQuadraticLatitudeJetSourceQuadraticBound

@[expose] public section

/-! The source mixed Palm upper scale from one common, selected coarea and
Laplace band. This avoids demanding the quadratic-bank estimate on every
physical band when the source only requires one sufficiently narrow band. -/

namespace SlowEquilibration.SphericalTAPMixedSourceUpperSelected
noncomputable section
open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
open SphericalQuadraticLatitudeJetCovariance
open SphericalTAPMixedQuadraticRealTransfer
open SphericalTAPMixedSourceBandShrink
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedBandScaleIdentity SphericalTAPMixedPhysicalRadialLower
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_mixed_energy_palm_upper_of_selected_coarea
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (mN : ℕ → ℝ) (L R ε b Cq C C₂ : ℝ)
    (hCq : 0 < Cq) (hC : 0 < C)
    (hRatio : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
        sourceMixedRadialLaplace d μ Q e L R ≤
        C*Real.exp (((d+2:ℕ):ℝ)*
          (β*e+(Real.log (1-Q)+β^2*residualAtOne μ Q)/2+
            C₂*(e-markE μ β x Q)^2))/Real.sqrt (d+2:ℕ))
    (hPalm : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
        sourceMixedEnergyPalmBandExpectation d μ Q β e L R
          (Real.sqrt Q) b' u hu ≤
          Cq*(latitudeNormalization (d+1)).toReal *
            (sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
              sourceMixedRadialLaplace d μ Q e L R)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ b' : ℝ, 0 < b' → b' ≤ b →
        ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          sourceMixedEnergyPalmBandExpectation d μ Q β e L R
            (Real.sqrt Q) b' u hu ≤
          C₁*sourceCriticalBandScale (d+1) μ h.overlap_range β (mN d) *
            Real.exp (β*(((d+2:ℕ):ℝ)*e-mN d)+
              ((d+2:ℕ):ℝ)*C₂*(e-markE μ β x Q)^2) := by
  let s : ℝ := 1-Q
  let A : ℝ := s^(-(3/2:ℝ))
  let C₁ : ℝ := Cq*C/A
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hA : 0 < A := Real.rpow_pos_of_pos hs _
  have hC₁ : 0 < C₁ := div_pos (mul_pos hCq hC) hA
  refine ⟨C₁,hC₁,?_⟩
  filter_upwards [hRatio,hPalm,Filter.eventually_ge_atTop 1] with d hd hp hd1
  intro b' hb' hbb' e he u hu
  let N : ℝ := ((d+2:ℕ):ℝ)
  let E := markE μ β x Q
  let F := (Real.log (1-Q)+β^2*residualAtOne μ Q)/2
  let J := sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b'
  let I := sourceMixedRadialLaplace d μ Q e L R
  let D := sourceCriticalBandScale (d+1) μ h.overlap_range β (mN d)
  have hlat : 0 ≤ (latitudeNormalization (d+1)).toReal := ENNReal.toReal_nonneg
  have hbase : β*e+F = CSParisiMeasure.variationalValue μ β+β*(e-E) := by
    have hh := h.variational_TAP
    dsimp [F,E] at *
    linarith
  have hscale := sourceMixed_bandScale_exact_identity μ h
    (d+1) (by omega) e (mN d)
  dsimp only at hscale
  have hscale' : D*Real.exp (β*(N*e-mN d)) =
      A*((latitudeNormalization (d+1)).toReal/Real.sqrt N)*
        Real.exp (N*(β*e+F)) := by
    simpa only [D,A,N,s,E,hbase] using hscale
  have hRN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by dsimp [N]; positivity)
  have hbaseExp : Real.exp (N*(β*e+F+C₂*(e-E)^2)) =
      Real.exp (N*(β*e+F))*Real.exp (N*C₂*(e-E)^2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hratio := hd b' hb' hbb' e he
  have hpalm := hp b' hb' hbb' e he u hu
  have hbound : sourceMixedEnergyPalmBandExpectation d μ Q β e L R
      (Real.sqrt Q) b' u hu ≤
      Cq*(latitudeNormalization (d+1)).toReal *
        (C*Real.exp (N*(β*e+F+C₂*(e-E)^2))/Real.sqrt N) := by
    exact hpalm.trans (mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hCq.le hlat))
  have hfactor :
      Cq*(latitudeNormalization (d+1)).toReal *
        (C*Real.exp (N*(β*e+F+C₂*(e-E)^2))/Real.sqrt N) =
      C₁*D*Real.exp (β*(N*e-mN d)+N*C₂*(e-E)^2) := by
    rw [Real.exp_add,hbaseExp]
    rw [show C₁*D* (Real.exp (β*(N*e-mN d)) *
      Real.exp (N*C₂*(e-E)^2)) =
      C₁*(D*Real.exp (β*(N*e-mN d)))*
        Real.exp (N*C₂*(e-E)^2) by ring,hscale']
    dsimp [C₁]
    field_simp
  exact hbound.trans_eq hfactor

/-- The mixed source upper bound on the literal energy-averaged Palm band.
The analytic Laplace band is shrunk to the actual quadratic-bank band before
the two estimates are combined. -/
theorem source_mixed_energy_palm_upper
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (mN : ℕ → ℝ) :
    ∃ L R ε b C₁ C₂ : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C₁ ∧ 0 < C₂ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ b' : ℝ, 0 < b' → b' ≤ b →
        ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          sourceMixedEnergyPalmBandExpectation d μ Q β e L R
            (Real.sqrt Q) b' u hu ≤
          C₁*sourceCriticalBandScale (d+1) μ h.overlap_range β (mN d) *
            Real.exp (β*(((d+2:ℕ):ℝ)*e-mN d)+
              ((d+2:ℕ):ℝ)*C₂*(e-markE μ β x Q)^2) := by
  obtain ⟨L,R,ε₀,b₀,C,C₂,hε₀,hb₀,hC,hC₂,hEdge,hLK,hKR,hband₀,hRatio₀⟩ :=
    mixed_source_joint_to_radial_ratio_upper μ h hnp
  let g := (L-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨bq,Cq,hbq,hbqQ,hCq,hQuad⟩ :=
    source_mb_quadratic_physicalMixedPalm μ hnp h hg
  have hL : sourceRadialEdge μ Q < L := by
    simpa only [sourceRadialEdge] using hEdge
  obtain ⟨εr,cR,hεr,hcR,hRadial⟩ :=
    sourceMixedRadialLaplace_nearby_lower μ h hnp hL ⟨hLK,hKR⟩
  let ε := min ε₀ εr
  let b := min b₀ bq
  have hε : 0 < ε := lt_min hε₀ hεr
  have hb : 0 < b := lt_min hb₀ hbq
  have hLR : L < R := hLK.trans hKR
  have hband : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 := by
    intro a ha
    apply hband₀
    exact ⟨by dsimp [b] at *; linarith [ha.1,min_le_left b₀ bq],
      by dsimp [b] at *; linarith [ha.2,min_le_left b₀ bq]⟩
  have hRatio : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
        sourceMixedRadialLaplace d μ Q e L R ≤
        C*Real.exp (((d+2:ℕ):ℝ)*
          (β*e+(Real.log (1-Q)+β^2*residualAtOne μ Q)/2+
            C₂*(e-markE μ β x Q)^2))/Real.sqrt (d+2:ℕ) := by
    filter_upwards [hRatio₀,hRadial] with d hd hr
    intro b' hb' hbb' e he
    have he₀ : e ∈ Icc (markE μ β x Q-ε₀) (markE μ β x Q+ε₀) := by
      exact ⟨by dsimp [ε] at *; linarith [he.1,min_le_left ε₀ εr],
        by dsimp [ε] at *; linarith [he.2,min_le_left ε₀ εr]⟩
    have her : e ∈ Icc (markE μ β x Q-εr) (markE μ β x Q+εr) := by
      exact ⟨by dsimp [ε] at *; linarith [he.1,min_le_right ε₀ εr],
        by dsimp [ε] at *; linarith [he.2,min_le_right ε₀ εr]⟩
    have hI : 0 < sourceMixedRadialLaplace d μ Q e L R :=
      lt_of_lt_of_le (by positivity) (hr e her)
    have hJ := sourceMixedJointLaplace_mono_band
      d μ h.overlap_range.1 β e L R (Real.sqrt Q) b' b₀
      hEdge hLR hb₀ (hbb'.trans (min_le_left b₀ bq)) hband₀
    exact (div_le_div_of_nonneg_right hJ hI.le).trans (hd e he₀)
  have hPalm : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
        sourceMixedEnergyPalmBandExpectation d μ Q β e L R
          (Real.sqrt Q) b' u hu ≤
          Cq*(latitudeNormalization (d+1)).toReal *
            (sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
              sourceMixedRadialLaplace d μ Q e L R) := by
    filter_upwards [hQuad,Filter.eventually_ge_atTop 1] with d hqd hd
    intro b' hb' hbb' e he u hu
    have hband' : Icc (Real.sqrt Q-b') (Real.sqrt Q+b') ⊆ Ioo (0:ℝ) 1 := by
      intro a ha
      apply hband
      exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
    apply mixed_quadratic_real_sections_to_energy_palm
      d hd μ h.overlap_range.1 hnp β e L R (Real.sqrt Q) b' Cq
      hEdge hLR hb' hCq.le hband' u hu
    intro k hk a ha
    have hkmark : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤
        (scorePairEquiv (e,k)) 1 := by
      simp only [scorePairEquiv_apply]
      dsimp [g]
      linarith [hk.1]
    have hh := hqd u hu (scorePairEquiv (e,k)) hkmark
      b' hb' (hbb'.trans (min_le_right b₀ bq)) a ha
    simpa [scorePairEquiv_apply] using hh
  obtain ⟨C₁,hC₁,hFinal⟩ := source_mixed_energy_palm_upper_of_selected_coarea
    μ h mN L R ε b Cq C C₂ hCq hC hRatio hPalm
  exact ⟨L,R,ε,b,C₁,C₂,hε,hb,hC₁,hC₂,hEdge,hLK,hKR,hband,hFinal⟩

end
end SlowEquilibration.SphericalTAPMixedSourceUpperSelected
