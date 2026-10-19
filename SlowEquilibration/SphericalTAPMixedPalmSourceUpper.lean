-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmDensityIdentity

@[expose] public section

/-! Exact mixed energy-Palm expectation for the original band partition.
The source Laplace ratio and the source `D_N` identity convert a uniform
coarea estimate into the printed Proposition 12.17 scale. -/

namespace SlowEquilibration.SphericalTAPMixedPalmSourceUpper
noncomputable section
open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalEnergyPalmAverage SphericalTAPCriticalBandSectionBridge
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPMixedSourceLaplaceRatio SphericalTAPMixedBandScaleIdentity
open SphericalTAPMixedPhysicalRadialLower
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The literal all-critical radial Palm mixture of the determinant-weighted
original partition on the physical latitude band. -/
def sourceMixedEnergyPalmBandExpectation
    (d : ℕ) (μ : FiniteMixture) (Q β e L R q b : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)) : ℝ :=
  ∫ k, (∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))
    ∂sourceAllCriticalRadialLaw d μ Q e L R

/-- Once the determinant–quadratic latitude section has been bounded and
physical coarea performed, the proved mixed two-variable Laplace ratio gives
the manuscript's exact `D_N` Palm upper scale.  The sole outstanding premise
is the intermediate coarea inequality on the literal Palm expectation. -/
theorem source_mixed_energy_palm_upper_of_coarea
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (mN : ℕ → ℝ)
    (hCoarea :
      ∀ (L R ε b : ℝ),
        0 < ε → 0 < b →
        2*Real.sqrt (Q^2*μ.xi2 Q) < L →
        L < markK μ β Q → markK μ β Q < R →
        Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 →
        ∃ Cq : ℝ, 0 < Cq ∧
          ∀ᶠ d : ℕ in atTop,
            ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
            ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
              sourceMixedEnergyPalmBandExpectation d μ Q β e L R
                (Real.sqrt Q) b u hu ≤
              Cq*(latitudeNormalization (d+1)).toReal *
                (sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b /
                  sourceMixedRadialLaplace d μ Q e L R)) :
    ∃ L R ε b C₁ C₂ : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C₁ ∧ 0 < C₂ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          sourceMixedEnergyPalmBandExpectation d μ Q β e L R
            (Real.sqrt Q) b u hu ≤
          C₁*sourceCriticalBandScale (d+1) μ h.overlap_range β (mN d) *
            Real.exp (β*(((d+2:ℕ):ℝ)*e-mN d)+
              ((d+2:ℕ):ℝ)*C₂*(e-markE μ β x Q)^2) := by
  obtain ⟨L,R,ε,b,C,C₂,hε,hb,hC,hC₂,hEdge,hLK,hKR,hband,hRatio⟩ :=
    mixed_source_joint_to_radial_ratio_upper μ h hnp
  obtain ⟨Cq,hCq,hPalm⟩ :=
    hCoarea L R ε b hε hb hEdge hLK hKR hband
  let s : ℝ := 1-Q
  let A : ℝ := s^(-(3/2:ℝ))
  let C₁ : ℝ := Cq*C/A
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hA : 0 < A := Real.rpow_pos_of_pos hs _
  have hC₁ : 0 < C₁ := div_pos (mul_pos hCq hC) hA
  refine ⟨L,R,ε,b,C₁,C₂,hε,hb,hC₁,hC₂,hEdge,hLK,hKR,hband,?_⟩
  filter_upwards [hRatio,hPalm,Filter.eventually_ge_atTop 1] with d hd hp hd1
  intro e he u hu
  let N : ℝ := ((d+2:ℕ):ℝ)
  let E := markE μ β x Q
  let F := (Real.log (1-Q)+β^2*residualAtOne μ Q)/2
  let J := sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b
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
  have hratio := hd e he
  have hpalm := hp e he u hu
  have hbound : sourceMixedEnergyPalmBandExpectation d μ Q β e L R
      (Real.sqrt Q) b u hu ≤
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

end
end SlowEquilibration.SphericalTAPMixedPalmSourceUpper
