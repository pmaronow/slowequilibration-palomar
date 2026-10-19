-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceQuadraticTangent

@[expose] public section

/-! The actual mixed exponent has zero directional derivative in every
physical `(k,a)` direction at the certified contact saddle. -/

namespace SlowEquilibration.SphericalTAPMixedContactGaussianCenter
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedLineCurvature
open SphericalTAPMixedLatitudeSmooth ConditionedEntrance
open SphericalTAPMixedSourceQuadraticTangent
set_option autoImplicit false

private theorem radialTheta_contDiff (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (radialTheta μ Q) := by
  unfold radialTheta monomialSum
  fun_prop

/-- The latitude derivative of the literal exponent is affine in its
radial score mark, including on the true physical logarithmic domain. -/
theorem mixed_latitude_first_from_zero
    (μ : FiniteMixture) (β Q e k a : ℝ) (ha : |a| < 1) :
    deriv (sourceMixedBandExponent μ β Q e k) a =
      deriv (sourceMixedBandExponent μ β Q e 0) a+
        β*k*deriv (radialTheta μ Q) a := by
  let G := sourceMixedBandExponent μ β Q e 0
  let r := radialTheta μ Q
  have hG : HasDerivAt G (deriv G a) a :=
    ((sourceMixedBandExponent_latitude_contDiffAt μ β Q e 0 a ha).differentiableAt
      (by norm_num)).hasDerivAt
  have hr : HasDerivAt r (deriv r a) a :=
    ((radialTheta_contDiff μ Q).differentiable (by norm_num) a).hasDerivAt
  have hfun : sourceMixedBandExponent μ β Q e k =
      (fun t => G t+(sourceRadialProfile μ Q e k-
        sourceRadialProfile μ Q e 0)+β*k*r t) := by
    funext t
    dsimp [G,r]
    unfold sourceMixedBandExponent sourceMixedXi sourceMixedMean
    ring
  rw [hfun]
  have hh := (hG.add_const (sourceRadialProfile μ Q e k-
    sourceRadialProfile μ Q e 0)).add (hr.const_mul (β*k))
  convert hh.deriv using 1

/-- At the certified mixed saddle, every line through the actual physical
contact has vanishing first derivative. -/
theorem mixed_contact_line_stationary
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (u v : ℝ) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    deriv (fun t => sourceMixedBandExponent μ β Q E (K+u*t) (q+v*t)) 0 = 0 := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  have hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < K :=
    sourceContact_markK_above_edge μ h
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hphysical : |q| < 1 := abs_lt.mpr ⟨by linarith,hq1⟩
  have hR : sourceRadialProfileDerivative μ Q E K = 0 :=
    sourceContact_radial_profile_derivative_zero μ h hnp
  have hr : radialTheta μ Q q = 0 := by
    simpa [q,sourceMixedMean] using
      (sourceMixedMean_contact μ h.overlap_range.1 hnp 0 1)
  have hlat : deriv (sourceMixedBandExponent μ β Q E K) q = 0 :=
    SphericalTAPMixedActualLatitudeStationarity.sourceMixedBandExponent_latitude_deriv_contact
      μ h hnp
  have hlat' := mixed_latitude_first_from_zero μ β Q E K q hphysical
  rw [hlat] at hlat'
  have hline := mixed_line_first μ β h.overlap_range.1 E K q u v 0
    (by simpa using hk) (by simpa using hphysical)
  have hline' : deriv (fun t =>
      sourceMixedBandExponent μ β Q E (K+u*t) (q+v*t)) 0 =
      u*sourceRadialProfileDerivative μ Q E K+
        v*deriv (sourceMixedBandExponent μ β Q E 0) q+
        β*(u*radialTheta μ Q q+K*v*deriv (radialTheta μ Q) q) := by
    simpa only [mul_zero,add_zero] using hline
  calc
    _ = u*sourceRadialProfileDerivative μ Q E K+
          v*deriv (sourceMixedBandExponent μ β Q E 0) q+
          β*(u*radialTheta μ Q q+K*v*deriv (radialTheta μ Q) q) := hline'
    _ = v*(deriv (sourceMixedBandExponent μ β Q E 0) q+
          β*K*deriv (radialTheta μ Q) q) := by rw [hR,hr]; ring
    _ = 0 := by rw [← hlat']; ring

/-- The actual mixed exponent is maximized at the source contact on one
physical rectangle and has a Gaussian quadratic drop there. -/
theorem mixed_source_contact_gaussian_upper
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    ∃ L R b0 cstar : ℝ,
      0 < b0 ∧ 0 < cstar ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ k ∈ Icc L R, ∀ a ∈ Icc (q-b0) (q+b0),
        sourceMixedBandExponent μ β Q E k a ≤
          sourceMixedBandExponent μ β Q E K q-
            cstar/2*((k-K)^2+(a-q)^2) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  obtain ⟨L,R,ε0,b0,cstar,hε0,hb0,hcstar,hLK,hKR,hI,htangent⟩ :=
    mixed_source_quadratic_tangent μ h hnp
  refine ⟨L,R,b0,cstar,hb0,hcstar,hLK,hKR,hI,?_⟩
  intro k hk a ha
  have he : E ∈ Icc (E-ε0) (E+ε0) := by constructor <;> linarith
  have hh := htangent E he k hk a ha
  rw [mixed_contact_line_stationary μ h hnp (k-K) (a-q)] at hh
  linarith

end
end SlowEquilibration.SphericalTAPMixedContactGaussianCenter
