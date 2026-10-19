-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPhysicalRadialLower

@[expose] public section

/-! The source mixed two-variable to one-variable Laplace ratio, with all
physical determinant, entropy, and energy-rate factors retained. -/

namespace SlowEquilibration.SphericalTAPMixedSourceLaplaceRatio
noncomputable section
open Set MeasureTheory Filter StrongFieldComplexity
open SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedSourceJointUpper
open SphericalTAPMixedPhysicalJointLaplace SphericalTAPMixedPhysicalRadialLower
open scoped Topology
set_option autoImplicit false

def sourceMixedJointLaplace (n : ℕ) (μ : FiniteMixture)
    (β Q e L R q b : ℝ) : ℝ :=
  ∫ z in (Icc L R) ×ˢ (Icc (q-b) (q+b)),
    sourceMixedJointIntegrand n μ β Q e z ∂planeVolume

/-- The mixed source Laplace ratio has only one surviving Gaussian width.
The exact physical contact identity and the optimized radial lower bound
produce the printed energy slope `β` without an implicit-function premise. -/
theorem mixed_source_joint_to_radial_ratio_upper
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
  obtain ⟨L,R,εJ,b,CJ,C₂,hεJ,hb,hCJ,hC₂,hEdgeL,hLK,hKR,hband,hJ⟩ :=
    mixed_source_physical_joint_laplace_upper μ h hnp
  have hL : sourceRadialEdge μ Q < L := by simpa only [sourceRadialEdge,edge] using hEdgeL
  have hm : K ∈ Ioo L R := ⟨hLK,hKR⟩
  obtain ⟨εR,cR,hεR,hcR,hR⟩ :=
    sourceMixedRadialLaplace_nearby_lower μ h hnp hL hm
  let ε := min εJ εR
  let C := CJ/cR
  have hε : 0 < ε := lt_min hεJ hεR
  have hC : 0 < C := div_pos hCJ hcR
  refine ⟨L,R,ε,b,C,C₂,hε,hb,hC,hC₂,hEdgeL,hLK,hKR,hband,?_⟩
  filter_upwards [hR] with n hn
  intro e he
  have heJ : e ∈ Icc (E-εJ) (E+εJ) := by
    have hh := min_le_left εJ εR
    exact ⟨by linarith [he.1],by linarith [he.2]⟩
  have heR : e ∈ Icc (E-εR) (E+εR) := by
    have hh := min_le_right εJ εR
    exact ⟨by linarith [he.1],by linarith [he.2]⟩
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
  have hJupper : J ≤ CJ*Real.exp (N*H)/N := hJ n e heJ
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

end
end SlowEquilibration.SphericalTAPMixedSourceLaplaceRatio
