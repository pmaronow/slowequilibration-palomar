-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedJointRectangleShrink
public import SlowEquilibration.SphericalTAPMixedCommonAnalyticChoice

/-! A source coarea rectangle can satisfy the score condition needed for the
all-critical energy envelope and the weighted joint Laplace upper bound at
the same time. The common rectangle is the intersection of two certified
rectangles, and the radial lower bound is taken on that intersection. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPMixedSourceCommonRatio

open Set MeasureTheory Filter StrongFieldComplexity
open SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedSourceJointUpper
open SphericalTAPMixedPhysicalJointLaplace SphericalTAPMixedPhysicalRadialLower
open SphericalTAPMixedSourceLaplaceRatio SphericalTAPMixedCommonAnalyticChoice
open SphericalTAPMixedJointRectangleShrink
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mixed_source_joint_to_radial_ratio_upper_common
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    let F := (Real.log (1-Q)+β^2*residualAtOne μ Q)/2
    ∃ L R ε b C C₂ : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C ∧ 0 < C₂ ∧
      edge < L ∧ L < K ∧ K < R ∧
      Icc (q-b) (q+b) ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ e ∈ Icc (E-ε) (E+ε), ∀ k ∈ Icc L R,
        β*x/2 ≤ sourceEnergySlope μ Q e k ∧
          sourceEnergySlope μ Q e k ≤ (β*x+β)/2) ∧
      ∀ᶠ n : ℕ in atTop, ∀ e ∈ Icc (E-ε) (E+ε),
        sourceMixedJointLaplace n μ β Q e L R q b /
          sourceMixedRadialLaplace n μ Q e L R ≤
          C*Real.exp ((n+2 : ℕ)*(β*e+F+C₂*(e-E)^2))/
            Real.sqrt (n+2 : ℕ) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  let F := (Real.log (1-Q)+β^2*residualAtOne μ Q)/2
  obtain ⟨LC,RC,εC,bC,ε₂,cstar,hεC,hbC,hbCq,hε₂,hε₂one,
    hcstar,hEdgeC,hLCK,hKRC,hbandC,hbankC,hbaseC,hHessC⟩ :=
    mixed_source_common_analytic_choice μ h hnp
  obtain ⟨LJ,RJ,εJ,bJ,CJ,C₂,hεJ,hbJ,hCJ,hC₂,hEdgeJ,hLJK,hKRJ,hbandJ,hJ⟩ :=
    mixed_source_physical_joint_laplace_upper μ h hnp
  let L := max LC LJ
  let R := min RC RJ
  have hEdge : edge < L := hEdgeC.trans_le (le_max_left _ _)
  have hLK : L < K := max_lt hLCK hLJK
  have hKR : K < R := lt_min hKRC hKRJ
  have hLR : L < R := hLK.trans hKR
  have hLrad : sourceRadialEdge μ Q < L := by
    simpa only [sourceRadialEdge,edge] using hEdge
  obtain ⟨εR,cR,hεR,hcR,hR⟩ :=
    sourceMixedRadialLaplace_nearby_lower μ h hnp hLrad ⟨hLK,hKR⟩
  let ε := min εC (min εJ εR)
  let b := min bC bJ
  let C := CJ/cR
  have hε : 0 < ε := lt_min hεC (lt_min hεJ hεR)
  have hb : 0 < b := lt_min hbC hbJ
  have hC : 0 < C := div_pos hCJ hcR
  have hband : Icc (q-b) (q+b) ⊆ Ioo (0 : ℝ) 1 := by
    intro a ha
    apply hbandC
    have hmin := min_le_left bC bJ
    exact ⟨by dsimp [b] at *; linarith [ha.1],
      by dsimp [b] at *; linarith [ha.2]⟩
  have hScore : ∀ e ∈ Icc (E-ε) (E+ε), ∀ k ∈ Icc L R,
        β*x/2 ≤ sourceEnergySlope μ Q e k ∧
          sourceEnergySlope μ Q e k ≤ (β*x+β)/2 := by
    intro e he k hk
    have heC : e ∈ Icc (E-εC) (E+εC) := by
      have hh := min_le_left εC (min εJ εR)
      exact ⟨by dsimp [ε] at *; linarith [he.1],
        by dsimp [ε] at *; linarith [he.2]⟩
    have hkC : k ∈ Icc LC RC :=
      ⟨(le_max_left _ _).trans hk.1,hk.2.trans (min_le_left _ _)⟩
    exact ⟨(hbaseC e heC k hkC).1,(hbaseC e heC k hkC).2.1⟩
  refine ⟨L,R,ε,b,C,C₂,hε,hb,hC,hC₂,hEdge,hLK,hKR,hband,hScore,?_⟩
  filter_upwards [hR] with n hn
  intro e he
  have heJ : e ∈ Icc (E-εJ) (E+εJ) := by
    have hh := (min_le_right εC (min εJ εR)).trans (min_le_left εJ εR)
    exact ⟨by dsimp [ε] at *; linarith [he.1],
      by dsimp [ε] at *; linarith [he.2]⟩
  have heR : e ∈ Icc (E-εR) (E+εR) := by
    have hh := (min_le_right εC (min εJ εR)).trans (min_le_right εJ εR)
    exact ⟨by dsimp [ε] at *; linarith [he.1],
      by dsimp [ε] at *; linarith [he.2]⟩
  let N : ℝ := (n+2 : ℕ)
  let θ := sourceSaddleComplexity μ Q e
  let H := sourceMixedBandExponent μ β Q e K q+C₂*(e-E)^2
  let M := β*e+F+C₂*(e-E)^2
  let J := sourceMixedJointLaplace n μ β Q e L R q b
  let I := sourceMixedRadialLaplace n μ Q e L R
  have hN : 0 < N := by dsimp [N]; positivity
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hIlower : cR*Real.exp (N*θ)/Real.sqrt N ≤ I := hn e heR
  have hI : 0 < I := lt_of_lt_of_le (by positivity) hIlower
  have hJmono : J ≤ sourceMixedJointLaplace n μ β Q e LJ RJ q bJ :=
    sourceMixedJointLaplace_mono_rectangle n μ h.overlap_range.1
      β e L R LJ RJ q b bJ hEdgeJ (hLJK.trans hKRJ) hbJ
      (le_max_right _ _) (min_le_right _ _) (min_le_right _ _) hbandJ
  have hJupper : J ≤ CJ*Real.exp (N*H)/N :=
    hJmono.trans (by simpa only [sourceMixedJointLaplace,N,H] using hJ n e heJ)
  have hU : 0 ≤ CJ*Real.exp (N*H)/N := by positivity
  have hLpos : 0 < cR*Real.exp (N*θ)/Real.sqrt N := by positivity
  have hheight : H-θ ≤ M := by
    have hcontact := sourceMixedBandExponent_contact μ
      (β := β) h.overlap_range.1 hnp e K
    have hmax := sourceRadialSaddle_global_max μ h hnp e K
    change sourceRadialProfile μ Q e K ≤ θ at hmax
    dsimp [H,M,F,K,q,θ]
    rw [hcontact]
    linarith
  have hexp : Real.exp (N*(H-θ)) ≤ Real.exp (N*M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hheight hN.le)
  calc
    J/I ≤ (CJ*Real.exp (N*H)/N)/I :=
      div_le_div_of_nonneg_right hJupper hI.le
    _ ≤ (CJ*Real.exp (N*H)/N)/
        (cR*Real.exp (N*θ)/Real.sqrt N) :=
      div_le_div_of_nonneg_left hU hLpos hIlower
    _ = C*Real.exp (N*(H-θ))/Real.sqrt N := by
      dsimp [C]
      rw [mul_sub, Real.exp_sub]
      field_simp
      nlinarith [Real.sq_sqrt hN.le]
    _ ≤ C*Real.exp (N*M)/Real.sqrt N := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hC.le) hsqrt.le

end SlowEquilibration.SphericalTAPMixedSourceCommonRatio
