-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPhysicalJointLaplace

@[expose] public section

/-! A certificate supplies a physical exterior score interval and latitude
band on which the literal mixed weighted two-variable integral has the
manuscript's `N⁻¹` Gaussian normalization, uniformly in nearby energies. -/

namespace SlowEquilibration.SphericalTAPMixedSourceJointUpper
noncomputable section
open Set MeasureTheory StrongFieldComplexity
open SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedNearbyGaussianCenter
open SphericalTAPMixedPhysicalChi SphericalTAPMixedPhysicalJointLaplace
set_option autoImplicit false

theorem mixed_source_physical_joint_laplace_upper
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ L R ε0 b0 C C₂ : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ 0 < C ∧ 0 < C₂ ∧
      edge < L ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ n : ℕ, ∀ e ∈ Icc (E-ε0) (E+ε0),
        (∫ z in (Icc L R) ×ˢ (Icc (q-b0) (q+b0)),
          sourceMixedJointIntegrand n μ β Q e z ∂planeVolume) ≤
          C*Real.exp ((n+2 : ℕ)*
            (sourceMixedBandExponent μ β Q e K q+C₂*(e-E)^2))/(n+2 : ℕ) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  obtain ⟨L,R,ε0,b0,cstar,C₂,hε0,hb0,hcstar,hC₂,hLK,hKR,hband,henv⟩ :=
    mixed_source_nearby_gaussian_upper μ h hnp
  have hEdge : edge < K := by
    simpa only [edge,K] using sourceContact_markK_above_edge μ h
  let L' := max L ((edge+K)/2)
  have hEdgeL' : edge < L' :=
    lt_of_lt_of_le (by linarith [hEdge]) (le_max_right L ((edge+K)/2))
  have hL'K : L' < K := max_lt hLK (by linarith [hEdge])
  have hsub : Icc L' R ⊆ Icc L R := by
    intro k hk
    exact ⟨(le_max_left L ((edge+K)/2)).trans hk.1,hk.2⟩
  obtain ⟨cχ,Cχ,hcχ,hCχ,hχ⟩ :=
    sourceMixedChi_bounds μ h.overlap_range.1 hEdgeL'
  let W₀ := (1-(q+b0)^2)^(-(3/2:ℝ))
  let c := cstar/4
  let C := Cχ*W₀*Real.pi/c
  have hqb : q+b0 < 1 := by
    have hpoint : q+b0 ∈ Icc (q-b0) (q+b0) := ⟨by linarith,le_refl _⟩
    exact (hband hpoint).2
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hW₀ : 0 < W₀ := Real.rpow_pos_of_pos (by nlinarith [hq0,hb0,hqb]) _
  have hc : 0 < c := by dsimp [c]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨L',R,ε0,b0,C,C₂,hε0,hb0,hC,hC₂,hEdgeL',hL'K,hKR,hband,?_⟩
  intro n e he
  have hχn (k : ℝ) (hk : k ∈ Icc L' R) :
      0 ≤ sourceMixedChi n μ Q k ∧ sourceMixedChi n μ Q k ≤ Cχ :=
    ⟨(hcχ.trans_le (hχ n k hk).1).le,(hχ n k hk).2⟩
  have henv' (k : ℝ) (hk : k ∈ Icc L' R)
      (a : ℝ) (ha : a ∈ Icc (q-b0) (q+b0)) :
      sourceMixedBandExponent μ β Q e k a ≤
        (sourceMixedBandExponent μ β Q e K q+C₂*(e-E)^2)-
          c*((k-K)^2+(a-q)^2) := by
    have hh := henv e he k (hsub hk) a ha
    dsimp [c]
    linarith
  have hh := sourceMixedJointIntegral_upper_of_envelope n μ
    (β := β) (Q := Q) (e := e) (L := L') (R := R)
    (K := K) (q := q) (b := b0) (c := c) (Cχ := Cχ)
    (H := sourceMixedBandExponent μ β Q e K q+C₂*(e-E)^2)
    hχn hCχ.le hc hb0 hband henv'
  simpa only [C,W₀] using hh

end
end SlowEquilibration.SphericalTAPMixedSourceJointUpper
