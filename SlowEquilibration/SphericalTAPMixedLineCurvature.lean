-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSaddleSource

@[expose] public section

/-! Restrict the literal mixed exponent to affine lines in the physical
`(k,a)` rectangle. This is the calculus bridge from the checked actual
Hessian to the two-dimensional Laplace bound. -/

namespace SlowEquilibration.SphericalTAPMixedLineCurvature
noncomputable section
open SphericalTAPMixedBandExponent SphericalTAPMixedJointHessianNeighborhood
open SphericalTAPMixedActualRadialHessian SphericalTAPMixedJointHessianContinuity
open SphericalTAPMixedLatitudeSmooth SphericalMarkedWindows ConditionedEntrance
open scoped Topology
set_option autoImplicit false

private theorem radialTheta_contDiff (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (radialTheta μ Q) := by
  unfold radialTheta monomialSum
  fun_prop

private theorem line_decomposition (μ : FiniteMixture) (β Q e k a : ℝ) :
    sourceMixedBandExponent μ β Q e k a =
      sourceMixedBandExponent μ β Q e 0 a+
        (sourceRadialProfile μ Q e k-sourceRadialProfile μ Q e 0)+
        β*k*radialTheta μ Q a := by
  unfold sourceMixedBandExponent sourceMixedXi sourceMixedMean
  ring

/-- The true line derivative uses the physical radial slope and the
latitude derivative of the literal exponent at zero radial mark. -/
theorem mixed_line_first
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a u v t : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k+u*t)
    (ha : |a+v*t| < 1) :
    deriv (fun s => sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s)) t =
      u*sourceRadialProfileDerivative μ Q e (k+u*t)+
        v*deriv (sourceMixedBandExponent μ β Q e 0) (a+v*t)+
        β*(u*radialTheta μ Q (a+v*t)+
          (k+u*t)*v*deriv (radialTheta μ Q) (a+v*t)) := by
  let K : ℝ → ℝ := fun s => k+u*s
  let A : ℝ → ℝ := fun s => a+v*s
  let R : ℝ → ℝ := sourceRadialProfile μ Q e
  let G : ℝ → ℝ := sourceMixedBandExponent μ β Q e 0
  let r : ℝ → ℝ := radialTheta μ Q
  have hK : HasDerivAt K u t := by
    simpa [K, id_eq, add_comm, mul_comm] using
      ((hasDerivAt_id t).const_mul u).const_add k
  have hA : HasDerivAt A v t := by
    simpa [A, id_eq, add_comm, mul_comm] using
      ((hasDerivAt_id t).const_mul v).const_add a
  have hR : HasDerivAt R (sourceRadialProfileDerivative μ Q e (K t)) (K t) := by
    convert sourceRadialProfile_hasDerivAt μ hQ e (K t) hk using 1
    rfl
  have hGdiff : DifferentiableAt ℝ G (A t) :=
    (sourceMixedBandExponent_latitude_contDiffAt μ β Q e 0 (A t) ha).differentiableAt
      (by norm_num)
  have hG : HasDerivAt G (deriv G (A t)) (A t) := hGdiff.hasDerivAt
  have hrdiff : DifferentiableAt ℝ r (A t) :=
    (radialTheta_contDiff μ Q).differentiable (by norm_num) (A t)
  have hr : HasDerivAt r (deriv r (A t)) (A t) := hrdiff.hasDerivAt
  have hsum : HasDerivAt
      (fun s => G (A s)+(R (K s)-R 0)+β*K s*r (A s))
      (v*deriv G (A t)+u*sourceRadialProfileDerivative μ Q e (K t)+
        β*(u*r (A t)+K t*(v*deriv r (A t)))) t := by
    convert ((hG.comp t hA).add ((hR.comp t hK).sub_const (R 0))).add
      ((((hK.mul (hr.comp t hA)).const_mul β))) using 1
    · funext s
      dsimp [Function.comp_def]
      ring
    · dsimp [Function.comp_def]
      ring
  have hfun : (fun s => sourceMixedBandExponent μ β Q e (K s) (A s)) =
      (fun s => G (A s)+(R (K s)-R 0)+β*K s*r (A s)) := by
    funext s
    exact line_decomposition μ β Q e (K s) (A s)
  rw [show (fun s => sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s)) =
      (fun s => sourceMixedBandExponent μ β Q e (K s) (A s)) from rfl,
    hfun,hsum.deriv]
  dsimp [K,A,R,G,r]
  ring

/-- The line second derivative is the literal quadratic form of the
three coordinate Hessian entries. -/
theorem mixed_line_second
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a u v t : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k+u*t)
    (ha : |a+v*t| < 1) :
    deriv (deriv (fun s =>
      sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s))) t =
      actualMixedHkk μ β Q ((e,k+u*t),a+v*t)*u^2+
        2*actualMixedHka μ β Q ((e,k+u*t),a+v*t)*u*v+
        actualMixedHaa μ β Q ((e,k+u*t),a+v*t)*v^2 := by
  let K : ℝ → ℝ := fun s => k+u*s
  let A : ℝ → ℝ := fun s => a+v*s
  let G : ℝ → ℝ := sourceMixedBandExponent μ β Q e 0
  let r : ℝ → ℝ := radialTheta μ Q
  let R' : ℝ → ℝ := sourceRadialProfileDerivative μ Q e
  have hK : HasDerivAt K u t := by
    simpa [K, id_eq, add_comm, mul_comm] using
      ((hasDerivAt_id t).const_mul u).const_add k
  have hA : HasDerivAt A v t := by
    simpa [A, id_eq, add_comm, mul_comm] using
      ((hasDerivAt_id t).const_mul v).const_add a
  have hR' : HasDerivAt R' (deriv R' (K t)) (K t) := by
    have hh := sourceRadialProfileDerivative_hasDerivAt μ hQ e (K t) hk
    change HasDerivAt (sourceRadialProfileDerivative μ Q e)
      (deriv (sourceRadialProfileDerivative μ Q e) (K t)) (K t)
    rw [hh.deriv]
    exact hh
  have hG' : HasDerivAt (deriv G) (deriv (deriv G) (A t)) (A t) := by
    have hcd : ContDiffAt ℝ 2 G (A t) :=
      (sourceMixedBandExponent_latitude_contDiffAt μ β Q e 0 (A t) ha).of_le
        (by norm_num)
    exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasDerivAt
  have hr : HasDerivAt r (deriv r (A t)) (A t) :=
    ((radialTheta_contDiff μ Q).differentiable (by norm_num) (A t)).hasDerivAt
  have hr' : HasDerivAt (deriv r) (deriv (deriv r) (A t)) (A t) := by
    have hcd : ContDiffAt ℝ 2 r (A t) :=
      (radialTheta_contDiff μ Q).contDiffAt.of_le (by norm_num)
    exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasDerivAt
  have hfirst : (fun s => deriv (fun z =>
      sourceMixedBandExponent μ β Q e (k+u*z) (a+v*z)) s) =ᶠ[𝓝 t]
      (fun s => u*R' (K s)+v*deriv G (A s)+
        β*(u*r (A s)+K s*v*deriv r (A s))) := by
    have hkn : ∀ᶠ s in 𝓝 t, 2*Real.sqrt (Q^2*μ.xi2 Q) < K s :=
      hK.continuousAt.eventually (isOpen_Ioi.mem_nhds hk)
    have han : ∀ᶠ s in 𝓝 t, |A s| < 1 := by
      have hh : A t ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp ha
      filter_upwards [hA.continuousAt.eventually (isOpen_Ioo.mem_nhds hh)]
        with s hs
      exact abs_lt.mpr hs
    filter_upwards [hkn,han] with s hks has
    exact mixed_line_first μ β hQ e k a u v s hks has
  have hrhs : HasDerivAt
      (fun s => u*R' (K s)+v*deriv G (A s)+
        β*(u*r (A s)+K s*v*deriv r (A s)))
      (u*(deriv R' (K t)*u)+v*(deriv (deriv G) (A t)*v)+
        β*(u*(deriv r (A t)*v)+
          u*v*deriv r (A t)+K t*v*(deriv (deriv r) (A t)*v))) t := by
    have hterm := (hK.mul_const v).mul (hr'.comp t hA)
    have hlat := ((hr.comp t hA).const_mul u).add hterm
    have htotal := (((hR'.comp t hK).const_mul u).add
      ((hG'.comp t hA).const_mul v)).add (hlat.const_mul β)
    convert htotal using 1
    · funext s
      dsimp [Function.comp_def]
    · dsimp [Function.comp_def]
      ring
  rw [hfirst.deriv_eq,hrhs.deriv]
  have hkk : actualMixedHkk μ β Q ((e,K t),A t) = deriv R' (K t) := by
    exact sourceMixedBandExponent_radial_second μ β hQ e (K t) (A t) hk
  have hka : actualMixedHka μ β Q ((e,K t),A t) =
      β*deriv r (A t) := by
    change deriv (fun t_1 => deriv
      (fun kk => sourceMixedBandExponent μ β Q e kk t_1) (K t)) (A t) = _
    rw [sourceMixedBandExponent_radial_latitude μ β hQ e (K t) (A t) hk,
      (radialTheta_hasDerivAt μ Q (A t)).deriv]
  have haa : actualMixedHaa μ β Q ((e,K t),A t) =
      deriv (deriv G) (A t)+β*K t*deriv (deriv r) (A t) := by
    have h1 :=
      SphericalTAPMixedJointLatitudeContinuity.sourceMixedBandExponent_latitude_second_affine
        μ β Q e (K t) (A t) ha
    have h0 :=
      SphericalTAPMixedJointLatitudeContinuity.sourceMixedBandExponent_latitude_second_affine
        μ β Q e 0 (A t) ha
    dsimp [G,r,actualMixedHaa]
    rw [h1,h0]
    ring
  dsimp [K,A,R',G,r] at *
  rw [hkk,hka,haa]
  ring

end
end SlowEquilibration.SphericalTAPMixedLineCurvature
