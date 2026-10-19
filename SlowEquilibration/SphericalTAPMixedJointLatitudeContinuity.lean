-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedActualEnergyCross

@[expose] public section

/-! Joint continuity of the literal mixed latitude Hessian in both marks
and latitude. The exponent is affine in `(e,k)` after two latitude
derivatives, so the result follows from the true polynomial regression row
and the physical log-domain smoothness. -/

namespace SlowEquilibration.SphericalTAPMixedJointLatitudeContinuity
noncomputable section
open Set SphericalTAPMixedBandExponent ConditionedEntrance SphericalMarkedWindows
open scoped Topology
set_option autoImplicit false

private theorem valueTheta_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (valueTheta μ Q) := by
  unfold valueTheta monomialSum
  fun_prop

private theorem radialTheta_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (radialTheta μ Q) := by
  unfold radialTheta monomialSum
  fun_prop

private theorem second_continuous (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
    Continuous (deriv (deriv f)) := by
  rw [continuous_iff_continuousAt]
  intro a
  have h2 : ContDiffAt ℝ 2 f a := hf.contDiffAt.of_le (by norm_num)
  have h1 : ContDiffAt ℝ 1 (deriv f) a := h2.derivWithin (by norm_num)
  have h0 : ContDiffAt ℝ 0 (deriv (deriv f)) a := h1.derivWithin (by norm_num)
  exact h0.continuousAt

/-- Exact affine dependence of the true second latitude derivative on the
two source marks, at each physical latitude. -/
theorem sourceMixedBandExponent_latitude_second_affine
    (μ : FiniteMixture) (β Q e k a : ℝ) (ha : |a| < 1) :
    deriv (deriv (sourceMixedBandExponent μ β Q e k)) a =
      deriv (deriv (sourceMixedBandExponent μ β Q 0 0)) a+
        β*e*deriv (deriv (valueTheta μ Q)) a+
        β*k*deriv (deriv (radialTheta μ Q)) a := by
  let c := sourceRadialProfile μ Q e k-sourceRadialProfile μ Q 0 0
  let g0 := sourceMixedBandExponent μ β Q 0 0
  let v := valueTheta μ Q
  let r := radialTheta μ Q
  have hfun : sourceMixedBandExponent μ β Q e k =
      fun t => c+(g0 t+β*e*v t+β*k*r t) := by
    funext t
    dsimp [c,g0,v,r,sourceMixedBandExponent,sourceMixedXi,sourceMixedMean]
    ring
  have hg0 : ContDiffAt ℝ 2 g0 a :=
    (SphericalTAPMixedLatitudeSmooth.sourceMixedBandExponent_latitude_contDiffAt
      μ β Q 0 0 a ha).of_le (by norm_num)
  have hv : ContDiffAt ℝ 2 v a :=
    (valueTheta_smooth μ Q).contDiffAt.of_le (by norm_num)
  have hr : ContDiffAt ℝ 2 r a :=
    (radialTheta_smooth μ Q).contDiffAt.of_le (by norm_num)
  have hβv : ContDiffAt ℝ 2 (fun t => β*e*v t) a := contDiffAt_const.mul hv
  have hβr : ContDiffAt ℝ 2 (fun t => β*k*r t) a := contDiffAt_const.mul hr
  have hgv : ContDiffAt ℝ 2 (fun t => g0 t+β*e*v t) a := hg0.add hβv
  have hinner : ContDiffAt ℝ 2
      (fun t => g0 t+β*e*v t+β*k*r t) a := hgv.add hβr
  have hiter (f : ℝ → ℝ) : iteratedDeriv 2 f a = deriv (deriv f) a := by
    simp [iteratedDeriv_eq_iterate, Function.iterate_succ_apply]
  rw [← hiter (sourceMixedBandExponent μ β Q e k),hfun]
  rw [← hiter g0,← hiter v,← hiter r]
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ))]
  have hsplit : (fun t => g0 t+β*e*v t+β*k*r t) =
      (fun t => g0 t+β*e*v t)+(fun t => β*k*r t) := rfl
  rw [hsplit,iteratedDeriv_add hgv hβr]
  have hsplit2 : (fun t => g0 t+β*e*v t) =
      g0+(fun t => β*e*v t) := rfl
  rw [hsplit2,iteratedDeriv_add hg0 hβv]
  simp only [iteratedDeriv_const_mul_field]

/-- The literal mixed latitude Hessian is jointly continuous in `(e,k,a)`
at every physical latitude, including the certified contact triple. -/
theorem sourceMixedBandExponent_latitude_second_joint_continuousAt
    (μ : FiniteMixture) (β Q e k a : ℝ) (ha : |a| < 1) :
    ContinuousAt (fun z : (ℝ × ℝ) × ℝ =>
      deriv (deriv (sourceMixedBandExponent μ β Q z.1.1 z.1.2)) z.2)
      ((e,k),a) := by
  let z0 : (ℝ × ℝ) × ℝ := ((e,k),a)
  let g0 := sourceMixedBandExponent μ β Q 0 0
  let v := valueTheta μ Q
  let r := radialTheta μ Q
  let F : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    deriv (deriv g0) z.2+
      β*z.1.1*deriv (deriv v) z.2+
      β*z.1.2*deriv (deriv r) z.2
  have ha0 : ContinuousAt (deriv (deriv g0)) a :=
    SphericalTAPMixedLatitudeSmooth.sourceMixedBandExponent_latitude_second_continuousAt
      μ β Q 0 0 a ha
  have hv0 : Continuous (deriv (deriv v)) :=
    second_continuous v (valueTheta_smooth μ Q)
  have hr0 : Continuous (deriv (deriv r)) :=
    second_continuous r (radialTheta_smooth μ Q)
  have hprojA : Continuous (fun z : (ℝ × ℝ) × ℝ => z.2) := continuous_snd
  have hprojE : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hprojK : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  have hF : ContinuousAt F z0 := by
    dsimp [F]
    fun_prop (disch := assumption)
  have hevent : (fun z : (ℝ × ℝ) × ℝ =>
      deriv (deriv (sourceMixedBandExponent μ β Q z.1.1 z.1.2)) z.2)
      =ᶠ[𝓝 z0] F := by
    have hband : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 z0, |z.2| < 1 := by
      exact hprojA.continuousAt.eventually (isOpen_Ioo.mem_nhds
        (show a ∈ Ioo (-1 : ℝ) 1 from abs_lt.mp ha)) |>.mono
          (by intro z hz; exact abs_lt.mpr hz)
    filter_upwards [hband] with z hz
    exact sourceMixedBandExponent_latitude_second_affine μ β Q z.1.1 z.1.2 z.2 hz
  exact hF.congr_of_eventuallyEq hevent

end
end SlowEquilibration.SphericalTAPMixedJointLatitudeContinuity
