-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLineDifferentiability

@[expose] public section

/-! The actual mixed exponent has a quantitative quadratic upper tangent
throughout one source-selected physical rectangle. -/

namespace SlowEquilibration.SphericalTAPMixedSourceQuadraticTangent
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedLineCurvature
open SphericalTAPMixedLineUniformCurvature
open SphericalTAPMixedLineDifferentiability
open SphericalTAPMixedQuadraticEnvelope
set_option autoImplicit false

private theorem affine_mem_Icc {L R k0 k1 t : ℝ}
    (hk0 : k0 ∈ Icc L R) (hk1 : k1 ∈ Icc L R)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    k0+(k1-k0)*t ∈ Icc L R := by
  have hs : k0+t • (k1-k0) ∈ Icc L R :=
    (convex_Icc L R).add_smul_mem hk0 (by convert hk1 using 1; ring) ht
  simpa only [smul_eq_mul,mul_comm t (k1-k0)] using hs

/-- A source certificate gives one rectangle on which the literal mixed
Laplace exponent lies below its tangent at `(K₀,√Q)` by a fixed Gaussian
quadratic. The tangent remains explicit along the actual exponent line. -/
theorem mixed_source_quadratic_tangent
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    ∃ L R ε0 b0 cstar : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ 0 < cstar ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε0) (E+ε0),
        ∀ k ∈ Icc L R, ∀ a ∈ Icc (q-b0) (q+b0),
          sourceMixedBandExponent μ β Q e k a ≤
            sourceMixedBandExponent μ β Q e K q+
              deriv (fun t => sourceMixedBandExponent μ β Q e
                (K+(k-K)*t) (q+(a-q)*t)) 0-
              cstar/2*((k-K)^2+(a-q)^2) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  obtain ⟨L,R,ε0,b0,cstar,hε0,hb0,hcstar,hedge,hLK,hKR,hI,hLine⟩ :=
    mixed_source_line_uniform_curvature μ h hnp
  refine ⟨L,R,ε0,b0,cstar,hε0,hb0,hcstar,hLK,hKR,hI,?_⟩
  intro e he k hk a ha
  let f : ℝ → ℝ := fun t => sourceMixedBandExponent μ β Q e
    (K+(k-K)*t) (q+(a-q)*t)
  have hKm : K ∈ Icc L R := ⟨hLK.le,hKR.le⟩
  have hqm : q ∈ Icc (q-b0) (q+b0) := by constructor <;> linarith
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      2*Real.sqrt (Q^2*μ.xi2 Q) < K+(k-K)*t ∧
        |q+(a-q)*t| < 1 := by
    have hkt : K+(k-K)*t ∈ Icc L R := affine_mem_Icc hKm hk ht
    have hat : q+(a-q)*t ∈ Icc (q-b0) (q+b0) :=
      affine_mem_Icc hqm ha ht
    exact ⟨hedge.trans_le hkt.1,
      abs_lt.mpr ⟨by linarith [(hI hat).1],(hI hat).2⟩⟩
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f t := by
    intro t ht
    obtain ⟨hkt,hat⟩ := hpath t ht
    exact mixed_line_differentiableAt μ β h.overlap_range.1 e K q
      (k-K) (a-q) t hkt hat
  have hf' : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv f) t := by
    intro t ht
    obtain ⟨hkt,hat⟩ := hpath t ht
    exact mixed_line_deriv_differentiableAt μ β h.overlap_range.1 e K q
      (k-K) (a-q) t hkt hat
  have hcurv : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv f) t ≤ -cstar*((k-K)^2+(a-q)^2) := by
    intro t ht
    exact hLine e he K hKm k hk q hqm a ha t ht
  have htangent := quadratic_upper_of_second_derivative
    (c := cstar*((k-K)^2+(a-q)^2)) hf hf' (by
      intro t ht
      linarith [hcurv t ht])
  have hzero : f 0 = sourceMixedBandExponent μ β Q e K q := by simp [f]
  have hone : f 1 = sourceMixedBandExponent μ β Q e k a := by simp [f]
  rw [hzero,hone] at htangent
  change sourceMixedBandExponent μ β Q e k a ≤
    sourceMixedBandExponent μ β Q e K q+deriv f 0-
      cstar/2*((k-K)^2+(a-q)^2)
  nlinarith [htangent]

end
end SlowEquilibration.SphericalTAPMixedSourceQuadraticTangent
