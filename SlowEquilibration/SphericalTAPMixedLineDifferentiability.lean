-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedQuadraticEnvelope

@[expose] public section

/-! Two genuine derivatives of the actual mixed exponent along every
physical exterior affine line, furnishing the regularity premises of the
quantitative tangent theorem. -/

namespace SlowEquilibration.SphericalTAPMixedLineDifferentiability
noncomputable section
open Set SphericalTAPMixedBandExponent SphericalTAPMixedLineCurvature
open SphericalTAPMixedLatitudeSmooth SphericalMarkedWindows ConditionedEntrance
open scoped Topology
set_option autoImplicit false

private theorem radialTheta_contDiff (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (radialTheta μ Q) := by
  unfold radialTheta monomialSum
  fun_prop

theorem mixed_line_differentiableAt
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a u v t : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k+u*t)
    (ha : |a+v*t| < 1) :
    DifferentiableAt ℝ (fun s =>
      sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s)) t := by
  let K : ℝ → ℝ := fun s => k+u*s
  let A : ℝ → ℝ := fun s => a+v*s
  let R : ℝ → ℝ := sourceRadialProfile μ Q e
  let G : ℝ → ℝ := sourceMixedBandExponent μ β Q e 0
  let r : ℝ → ℝ := radialTheta μ Q
  have hK : DifferentiableAt ℝ K t := by fun_prop
  have hA : DifferentiableAt ℝ A t := by fun_prop
  have hR : DifferentiableAt ℝ R (K t) :=
    (sourceRadialProfile_hasDerivAt μ hQ e (K t) hk).differentiableAt
  have hG : DifferentiableAt ℝ G (A t) :=
    (sourceMixedBandExponent_latitude_contDiffAt μ β Q e 0 (A t) ha).differentiableAt
      (by norm_num)
  have hr : DifferentiableAt ℝ r (A t) :=
    (radialTheta_contDiff μ Q).differentiable (by norm_num) (A t)
  have hline : DifferentiableAt ℝ
      (fun s => G (A s)+(R (K s)-R 0)+β*K s*r (A s)) t := by
    fun_prop (disch := assumption)
  have hfun : (fun s => sourceMixedBandExponent μ β Q e (K s) (A s)) =
      (fun s => G (A s)+(R (K s)-R 0)+β*K s*r (A s)) := by
    funext s
    dsimp [G,R,r]
    unfold sourceMixedBandExponent sourceMixedXi sourceMixedMean
    ring
  rw [show (fun s => sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s)) =
      (fun s => sourceMixedBandExponent μ β Q e (K s) (A s)) from rfl,hfun]
  exact hline

theorem mixed_line_deriv_differentiableAt
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a u v t : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k+u*t)
    (ha : |a+v*t| < 1) :
    DifferentiableAt ℝ (deriv (fun s =>
      sourceMixedBandExponent μ β Q e (k+u*s) (a+v*s))) t := by
  let K : ℝ → ℝ := fun s => k+u*s
  let A : ℝ → ℝ := fun s => a+v*s
  let R' : ℝ → ℝ := sourceRadialProfileDerivative μ Q e
  let G : ℝ → ℝ := sourceMixedBandExponent μ β Q e 0
  let r : ℝ → ℝ := radialTheta μ Q
  have hK : ContinuousAt K t := by fun_prop
  have hA : ContinuousAt A t := by fun_prop
  have hR' : DifferentiableAt ℝ R' (K t) :=
    (sourceRadialProfileDerivative_hasDerivAt μ hQ e (K t) hk).differentiableAt
  have hG' : DifferentiableAt ℝ (deriv G) (A t) := by
    have hcd : ContDiffAt ℝ 2 G (A t) :=
      (sourceMixedBandExponent_latitude_contDiffAt μ β Q e 0 (A t) ha).of_le
        (by norm_num)
    exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ r (A t) :=
    (radialTheta_contDiff μ Q).differentiable (by norm_num) (A t)
  have hr' : DifferentiableAt ℝ (deriv r) (A t) := by
    have hcd : ContDiffAt ℝ 2 r (A t) :=
      (radialTheta_contDiff μ Q).contDiffAt.of_le (by norm_num)
    exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hkn : ∀ᶠ s in 𝓝 t, 2*Real.sqrt (Q^2*μ.xi2 Q) < K s :=
    hK.eventually (isOpen_Ioi.mem_nhds hk)
  have han : ∀ᶠ s in 𝓝 t, |A s| < 1 := by
    have hh : A t ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp ha
    filter_upwards [hA.eventually (isOpen_Ioo.mem_nhds hh)] with s hs
    exact abs_lt.mpr hs
  have hfirst : deriv (fun z =>
      sourceMixedBandExponent μ β Q e (k+u*z) (a+v*z)) =ᶠ[𝓝 t]
      (fun s => u*R' (K s)+v*deriv G (A s)+
        β*(u*r (A s)+K s*v*deriv r (A s))) := by
    filter_upwards [hkn,han] with s hks has
    exact mixed_line_first μ β hQ e k a u v s hks has
  have hRHS : DifferentiableAt ℝ
      (fun s => u*R' (K s)+v*deriv G (A s)+
        β*(u*r (A s)+K s*v*deriv r (A s))) t := by
    fun_prop (disch := assumption)
  exact hRHS.congr_of_eventuallyEq hfirst

end
end SlowEquilibration.SphericalTAPMixedLineDifferentiability
