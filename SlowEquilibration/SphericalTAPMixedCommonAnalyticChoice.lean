-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedJointHessianNeighborhood
public import SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood

@[expose] public section

/-! A single mixed source choice combines the certified energy slope,
radial curvature, quadratic-bank margin, and the literal joint `(k,a)`
Hessian gap. -/

namespace SlowEquilibration.SphericalTAPMixedCommonAnalyticChoice
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPCriticalAnalyticNeighborhood
open SphericalTAPMixedJointHessianNeighborhood
set_option autoImplicit false

theorem mixed_source_common_analytic_choice
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ L R ε0 b0 ε2 cstar : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ b0 < q ∧ 0 < ε2 ∧ ε2 < 1 ∧
      0 < cstar ∧ edge < L ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ b : ℝ, 0 < b → b ≤ b0 →
        ∀ a ∈ Icc (q-b) (q+b),
          2*β^2*sourceQuadraticLatitudeVariance μ a ≤ 1-ε2) ∧
      (∀ e ∈ Icc (E-ε0) (E+ε0), ∀ k ∈ Icc L R,
        (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2 ∧
        deriv (sourceRadialProfileDerivative μ Q e) k ≤ -cstar) ∧
      (∀ e ∈ Icc (E-ε0) (E+ε0), ∀ k ∈ Icc L R,
        ∀ a ∈ Icc (q-b0) (q+b0), ∀ u v : ℝ,
          actualMixedHkk μ β Q ((e,k),a)*u^2+
            2*actualMixedHka μ β Q ((e,k),a)*u*v+
            actualMixedHaa μ β Q ((e,k),a)*v^2 ≤
              -cstar*(u^2+v^2)) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  obtain ⟨Lg,Rg,εg,bg,ε2,cr,hεg,hbg,hbgq,hε2,hε2one,hcr,
    hEdge,hLgK,hKRg,hI,hbank,hbase⟩ :=
    mixed_source_slope_radial_and_quadratic_choice μ h hnp
  obtain ⟨εH,bH,cH,hεH,hbH,hcH,hHess⟩ :=
    actual_mixed_hessian_uniform_negative_neighborhood μ h hnp
  let L := max Lg (K-εH/2)
  let R := min Rg (K+εH/2)
  let ε0 := min εg εH
  let b0 := min bg bH
  let cstar := min cr cH
  have hε0 : 0 < ε0 := lt_min hεg hεH
  have hb0 : 0 < b0 := lt_min hbg hbH
  have hcstar : 0 < cstar := lt_min hcr hcH
  have hLc : L < K := max_lt hLgK (by dsimp [L,K]; linarith [hεH])
  have hRc : K < R := lt_min hKRg (by dsimp [R,K]; linarith [hεH])
  have hEdgeL : 2*Real.sqrt (Q^2*μ.xi2 Q) < L :=
    hEdge.trans_le (le_max_left _ _)
  refine ⟨L,R,ε0,b0,ε2,cstar,hε0,hb0,?_,hε2,hε2one,hcstar,
    hEdgeL,hLc,hRc,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) hbgq
  · intro a ha
    apply hI
    have hmin := min_le_left bg bH
    constructor <;> dsimp [b0] at * <;> linarith [ha.1,ha.2]
  · intro b hb hbb a ha
    exact hbank b hb (hbb.trans (min_le_left _ _)) a ha
  · intro e he k hk
    have he' : e ∈ Icc (E-εg) (E+εg) := by
      have hh := min_le_left εg εH
      constructor <;> dsimp [ε0] at * <;> linarith [he.1,he.2]
    have hk' : k ∈ Icc Lg Rg := by
      constructor
      · exact (le_max_left _ _).trans hk.1
      · exact hk.2.trans (min_le_left _ _)
    obtain ⟨hlo,hhi,hcurv⟩ := hbase e he' k hk'
    refine ⟨hlo,hhi,?_⟩
    have hh := min_le_left cr cH
    dsimp [cstar]
    linarith
  · intro e he k hk a ha u v
    have heAbs : |e-E| ≤ εH := by
      apply abs_le.mpr
      have hmin := min_le_right εg εH
      constructor <;> dsimp [ε0] at * <;> linarith [he.1,he.2]
    have hkAbs : |k-K| ≤ εH := by
      apply abs_le.mpr
      have hll := le_max_right Lg (K-εH/2)
      have hrr := min_le_right Rg (K+εH/2)
      constructor <;> dsimp [L,R] at * <;> linarith [hk.1,hk.2,hεH]
    have haAbs : |a-q| ≤ bH := by
      apply abs_le.mpr
      have hmin := min_le_right bg bH
      constructor <;> dsimp [b0] at * <;> linarith [ha.1,ha.2]
    obtain ⟨_,_,hcurv⟩ := hHess e k a heAbs hkAbs haAbs
    have hquant := hcurv u v
    have hnorm : 0 ≤ u^2+v^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hmin := min_le_right cr cH
    dsimp [cstar]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmin) hnorm]

end
end SlowEquilibration.SphericalTAPMixedCommonAnalyticChoice
