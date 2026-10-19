-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedContactGaussianCenter

@[expose] public section

/-! Fixed-center Gaussian control for every nearby energy, obtained from
the source's exact affine energy dependence and the mixed Hessian gap. -/

namespace SlowEquilibration.SphericalTAPMixedNearbyGaussianCenter
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedLineCurvature
open SphericalTAPMixedLatitudeSmooth ConditionedEntrance
open SphericalTAPMixedSourceQuadraticTangent
open SphericalTAPMixedContactGaussianCenter
set_option autoImplicit false

/-- At the physical contact latitude and fixed contact radial mark, the
latitude derivative of the literal joint exponent vanishes for every
energy. Its energy coefficient has zero latitude derivative exactly. -/
theorem mixed_contact_latitude_stationary_all_energy
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) :
    deriv (sourceMixedBandExponent μ β Q e (markK μ β Q)) (Real.sqrt Q)=0 := by
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hphysical : |q| < 1 := abs_lt.mpr ⟨by linarith,hq1⟩
  have hG : HasDerivAt (sourceMixedBandExponent μ β Q E K)
      (deriv (sourceMixedBandExponent μ β Q E K) q) q :=
    ((sourceMixedBandExponent_latitude_contDiffAt μ β Q E K q hphysical).differentiableAt
      (by norm_num)).hasDerivAt
  have hV := valueTheta_hasDerivAt μ Q q
  have hfun : sourceMixedBandExponent μ β Q e K =
      fun t => sourceMixedBandExponent μ β Q E K t+
        (sourceRadialProfile μ Q e K-sourceRadialProfile μ Q E K)+
        β*(e-E)*valueTheta μ Q t := by
    funext t
    unfold sourceMixedBandExponent sourceMixedXi sourceMixedMean
    ring
  rw [show markK μ β Q = K from rfl, hfun]
  have hh := (hG.add_const (sourceRadialProfile μ Q e K-
    sourceRadialProfile μ Q E K)).add (hV.const_mul (β*(e-E)))
  change HasDerivAt (fun t => sourceMixedBandExponent μ β Q E K t+
    (sourceRadialProfile μ Q e K-sourceRadialProfile μ Q E K)+
    β*(e-E)*valueTheta μ Q t)
      (deriv (sourceMixedBandExponent μ β Q E K) q+
        β*(e-E)*valueThetaDerivative μ Q q) q at hh
  rw [hh.deriv]
  rw [SphericalTAPMixedActualLatitudeStationarity.sourceMixedBandExponent_latitude_deriv_contact
    μ h hnp]
  rw [(SphericalTAPMixedContactDerivatives.mixed_regression_row_derivative_contact
    μ h.overlap_range.1 hnp).1]
  ring

/-- At the fixed contact radial mark, the true radial derivative varies
affinely with energy with its literal inverse-covariance coefficient. -/
theorem mixed_contact_radial_energy_affine
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) :
    sourceRadialProfileDerivative μ Q e (markK μ β Q) =
      -((((μ.scoreCovariance Q)⁻¹) 0 1+
        ((μ.scoreCovariance Q)⁻¹) 1 0)/2)*(e-markE μ β x Q) := by
  have hstationary := sourceContact_radial_profile_derivative_zero μ h hnp
  unfold sourceRadialProfileDerivative sourceRadialSlope at *
  linear_combination hstationary

/-- The actual directional tangent at `(K₀,√Q)` is purely radial and
exactly linear in the energy displacement. -/
theorem mixed_nearby_contact_line_tangent
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e u v : ℝ) :
    let K := markK μ β Q
    let q := Real.sqrt Q
    let A := (((μ.scoreCovariance Q)⁻¹) 0 1+
      ((μ.scoreCovariance Q)⁻¹) 1 0)/2
    deriv (fun t => sourceMixedBandExponent μ β Q e (K+u*t) (q+v*t)) 0 =
      -A*(e-markE μ β x Q)*u := by
  dsimp only
  let K := markK μ β Q
  let q := Real.sqrt Q
  let A := (((μ.scoreCovariance Q)⁻¹) 0 1+
    ((μ.scoreCovariance Q)⁻¹) 1 0)/2
  have hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < K :=
    sourceContact_markK_above_edge μ h
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hphysical : |q| < 1 := abs_lt.mpr ⟨by linarith,hq1⟩
  have hR := mixed_contact_radial_energy_affine μ h hnp e
  have hr : radialTheta μ Q q = 0 := by
    simpa [q,sourceMixedMean] using
      (sourceMixedMean_contact μ h.overlap_range.1 hnp 0 1)
  have hlat := mixed_contact_latitude_stationary_all_energy μ h hnp e
  have hlat' := mixed_latitude_first_from_zero μ β Q e K q hphysical
  rw [hlat] at hlat'
  have hline := mixed_line_first μ β h.overlap_range.1 e K q u v 0
    (by simpa using hk) (by simpa using hphysical)
  have hline' : deriv (fun t =>
      sourceMixedBandExponent μ β Q e (K+u*t) (q+v*t)) 0 =
      u*sourceRadialProfileDerivative μ Q e K+
        v*deriv (sourceMixedBandExponent μ β Q e 0) q+
        β*(u*radialTheta μ Q q+K*v*deriv (radialTheta μ Q) q) := by
    simpa only [mul_zero,add_zero] using hline
  rw [hR,hr] at hline'
  dsimp [A,K,q] at *
  linear_combination hline' - v*hlat'

/-- Uniform Gaussian decay of the literal mixed exponent around the fixed
source contact, with only a quadratic energy-displacement loss. This avoids
choosing an energy-dependent maximizer in the upper Laplace integral. -/
theorem mixed_source_nearby_gaussian_upper
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    ∃ L R ε0 b0 cstar C : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ 0 < cstar ∧ 0 < C ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε0) (E+ε0),
        ∀ k ∈ Icc L R, ∀ a ∈ Icc (q-b0) (q+b0),
          sourceMixedBandExponent μ β Q e k a ≤
            sourceMixedBandExponent μ β Q e K q+
              C*(e-E)^2-cstar/4*((k-K)^2+(a-q)^2) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  let A := (((μ.scoreCovariance Q)⁻¹) 0 1+
    ((μ.scoreCovariance Q)⁻¹) 1 0)/2
  obtain ⟨L,R,ε0,b0,cstar,hε0,hb0,hcstar,hLK,hKR,hI,htangent⟩ :=
    mixed_source_quadratic_tangent μ h hnp
  let C := 1+A^2/cstar
  have hC : 0 < C := by
    dsimp [C]
    have hh : 0 ≤ A^2/cstar := div_nonneg (sq_nonneg _) hcstar.le
    linarith
  refine ⟨L,R,ε0,b0,cstar,C,hε0,hb0,hcstar,hC,hLK,hKR,hI,?_⟩
  intro e he k hk a ha
  have htan := htangent e he k hk a ha
  rw [mixed_nearby_contact_line_tangent μ h hnp e (k-K) (a-q)] at htan
  let d := e-E
  let p := k-K
  let w := a-q
  have hcore : 0 ≤ C*d^2+A*d*p+cstar/4*(p^2+w^2) := by
    have hident : 4*cstar*(C*d^2+A*d*p+cstar/4*(p^2+w^2)) =
        (2*A*d+cstar*p)^2+cstar^2*w^2+4*cstar*d^2 := by
      dsimp [C]
      field_simp [hcstar.ne']
      ring
    have hsum : 0 ≤ (2*A*d+cstar*p)^2+cstar^2*w^2+4*cstar*d^2 := by
      have hw : 0 ≤ cstar^2*w^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hd : 0 ≤ 4*cstar*d^2 := by positivity
      nlinarith [sq_nonneg (2*A*d+cstar*p)]
    have hmul : 0 ≤ 4*cstar*(C*d^2+A*d*p+cstar/4*(p^2+w^2)) := by
      rw [hident]
      exact hsum
    by_contra hn
    have hneg : C*d^2+A*d*p+cstar/4*(p^2+w^2) < 0 := lt_of_not_ge hn
    have hprod := mul_neg_of_pos_of_neg (by positivity : 0 < 4*cstar) hneg
    linarith
  dsimp [C,d,p,w] at hcore ⊢
  dsimp [A,E,K,q] at hcore
  dsimp [E,K,q] at htan
  nlinarith [htan]

end
end SlowEquilibration.SphericalTAPMixedNearbyGaussianCenter
