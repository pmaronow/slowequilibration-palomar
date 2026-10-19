-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedJointLatitudeContinuity

@[expose] public section

/-! Joint continuity of the other two actual mixed Hessian entries on the
exterior radial region. -/

namespace SlowEquilibration.SphericalTAPMixedJointHessianContinuity
noncomputable section
open Set SphericalTAPMixedBandExponent ConditionedEntrance SphericalMarkedWindows
open scoped Topology
set_option autoImplicit false

private theorem resolventSquare_exterior_eq {z : ℝ} (hz : 2 < z) :
    SemicirclePotential.resolventSquare z =
      (z*SemicirclePotential.resolvent z-2)/(4-z^2) := by
  have hden : 4-z^2 ≠ 0 := ne_of_lt (by nlinarith)
  apply (eq_div_iff hden).mpr
  have hh := SemicirclePotential.resolvent_integration_by_parts hz
  linear_combination hh

private theorem resolventSquare_continuousAt {z : ℝ} (hz : 2 < z) :
    ContinuousAt SemicirclePotential.resolventSquare z := by
  have hden : 4-z^2 ≠ 0 := ne_of_lt (by nlinarith)
  have hres : ContinuousAt SemicirclePotential.resolvent z :=
    (SemicirclePotential.resolvent_hasDerivAt hz).continuousAt
  have hrat : ContinuousAt
      (fun t => (t*SemicirclePotential.resolvent t-2)/(4-t^2)) z := by
    fun_prop (disch := assumption)
  have hevent : SemicirclePotential.resolventSquare =ᶠ[𝓝 z]
      (fun t => (t*SemicirclePotential.resolvent t-2)/(4-t^2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact resolventSquare_exterior_eq ht
  exact hrat.congr_of_eventuallyEq hevent

private theorem radial_curvature_continuousAt (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) {k : ℝ}
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ContinuousAt (fun kk => -sourceRadialCurvature μ Q-
      SemicirclePotential.resolventSquare
        (kk/Real.sqrt (Q^2*μ.xi2 Q))/(Q^2*μ.xi2 Q)) k := by
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hs : 0 < Real.sqrt (Q^2*μ.xi2 Q) := Real.sqrt_pos.mpr hb
  have hz : 2 < k/Real.sqrt (Q^2*μ.xi2 Q) :=
    (lt_div_iff₀ hs).mpr hk
  have harg : ContinuousAt
      (fun kk : ℝ => kk/Real.sqrt (Q^2*μ.xi2 Q)) k := by fun_prop
  have hres : ContinuousAt (fun kk : ℝ =>
      SemicirclePotential.resolventSquare
        (kk/Real.sqrt (Q^2*μ.xi2 Q))) k := by
    have hh : ContinuousAt
        (SemicirclePotential.resolventSquare ∘
          fun kk : ℝ => kk/Real.sqrt (Q^2*μ.xi2 Q)) k :=
      ContinuousAt.comp (f := fun kk : ℝ => kk/Real.sqrt (Q^2*μ.xi2 Q))
        (g := SemicirclePotential.resolventSquare) (resolventSquare_continuousAt hz)
        harg
    exact hh
  have hb0 : Q^2*μ.xi2 Q ≠ 0 := hb.ne'
  fun_prop (disch := assumption)

/-- The actual radial-radial Hessian entry of `g` is jointly continuous in
`((e,k),a)` at every exterior radial mark. -/
theorem sourceMixedBandExponent_radial_second_joint_continuousAt
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ContinuousAt (fun z : (ℝ × ℝ) × ℝ =>
      deriv (deriv (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk z.2)) z.1.2)
      ((e,k),a) := by
  let z0 : (ℝ × ℝ) × ℝ := ((e,k),a)
  let R : ℝ → ℝ := fun kk => -sourceRadialCurvature μ Q-
    SemicirclePotential.resolventSquare
      (kk/Real.sqrt (Q^2*μ.xi2 Q))/(Q^2*μ.xi2 Q)
  have hkproj : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  have hR : ContinuousAt R k := radial_curvature_continuousAt μ hQ hk
  have hRjoint : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => R z.1.2) z0 := by
    have hh : ContinuousAt (R ∘ fun z : (ℝ × ℝ) × ℝ => z.1.2) z0 :=
      ContinuousAt.comp (f := fun z : (ℝ × ℝ) × ℝ => z.1.2)
        (g := R) hR hkproj.continuousAt
    exact hh
  have hevent : (fun z : (ℝ × ℝ) × ℝ =>
      deriv (deriv (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk z.2)) z.1.2)
      =ᶠ[𝓝 z0] (fun z => R z.1.2) := by
    have hb : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0,
        2*Real.sqrt (Q^2*μ.xi2 Q) < z.1.2 := by
      exact hkproj.continuousAt.eventually (isOpen_Ioi.mem_nhds hk)
    filter_upwards [hb] with z hz
    rw [SphericalTAPMixedActualRadialHessian.sourceMixedBandExponent_radial_second
      μ β hQ z.1.1 z.1.2 z.2 hz,
      (sourceRadialProfileDerivative_hasDerivAt μ hQ z.1.1 z.1.2 hz).deriv]
  exact hRjoint.congr_of_eventuallyEq hevent

/-- The actual mixed radial-latitude entry is the derivative of the true
regression multiplier at every exterior point. -/
theorem sourceMixedBandExponent_radial_latitude
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun t => deriv
      (fun kk => sourceMixedBandExponent μ β Q e kk t) k) a =
      β*radialThetaDerivative μ Q a := by
  have hfun : (fun t => deriv
      (fun kk => sourceMixedBandExponent μ β Q e kk t) k) =
      fun t => sourceRadialProfileDerivative μ Q e k+β*radialTheta μ Q t := by
    funext t
    exact SphericalTAPMixedActualRadialHessian.sourceMixedBandExponent_radial_first
      μ β hQ e k t hk
  rw [hfun]
  have hh := ((radialTheta_hasDerivAt μ Q a).const_mul β).const_add
    (sourceRadialProfileDerivative μ Q e k)
  exact hh.deriv

/-- The actual mixed radial-latitude entry is jointly continuous in the
three source variables throughout the exterior region. -/
theorem sourceMixedBandExponent_radial_latitude_joint_continuousAt
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (e k a : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ContinuousAt (fun z : (ℝ × ℝ) × ℝ =>
      deriv (fun t => deriv
        (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk t) z.1.2) z.2)
      ((e,k),a) := by
  let z0 : (ℝ × ℝ) × ℝ := ((e,k),a)
  have hθ : Continuous (radialThetaDerivative μ Q) := by
    unfold radialThetaDerivative monomialSum
    fun_prop
  have hprojA : Continuous (fun z : (ℝ × ℝ) × ℝ => z.2) := continuous_snd
  have hR : ContinuousAt
      (fun z : (ℝ × ℝ) × ℝ => β*radialThetaDerivative μ Q z.2) z0 := by
    fun_prop
  have hevent : (fun z : (ℝ × ℝ) × ℝ =>
      deriv (fun t => deriv
        (fun kk => sourceMixedBandExponent μ β Q z.1.1 kk t) z.1.2) z.2)
      =ᶠ[𝓝 z0] (fun z => β*radialThetaDerivative μ Q z.2) := by
    have hkproj : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
      continuous_snd.comp continuous_fst
    have hb : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0,
        2*Real.sqrt (Q^2*μ.xi2 Q) < z.1.2 :=
      hkproj.continuousAt.eventually (isOpen_Ioi.mem_nhds hk)
    filter_upwards [hb] with z hz
    exact sourceMixedBandExponent_radial_latitude μ β hQ z.1.1 z.1.2 z.2 hz
  exact hR.congr_of_eventuallyEq hevent

end
end SlowEquilibration.SphericalTAPMixedJointHessianContinuity
