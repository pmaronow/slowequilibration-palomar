-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedMeanContactSecond

@[expose] public section

/-! The literal gradient-regression reduction has the manuscript's contact
second derivative. -/

namespace SlowEquilibration.SphericalTAPMixedGradientSecond
noncomputable section
open SphericalTAPMixedBandExponent
set_option autoImplicit false

private theorem factor_hasDerivAt (a : ℝ) :
    HasDerivAt (fun t : ℝ => 1-t^2) (-2*a) a := by
  convert (hasDerivAt_const a 1).sub ((hasDerivAt_id a).pow 2) using 1
  · ext t
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

theorem sourceMixedGradientReduction_first (μ : FiniteMixture) (Q a : ℝ) :
    deriv (sourceMixedGradientReduction μ Q) a =
      (-2*a*(μ.xi1 (Real.sqrt Q*a))^2+
        (1-a^2)*2*μ.xi1 (Real.sqrt Q*a)*Real.sqrt Q*
          μ.xi2 (Real.sqrt Q*a))/μ.xi1 Q := by
  let q := Real.sqrt Q
  let f : ℝ → ℝ := fun t => μ.xi1 (q*t)
  have hf : HasDerivAt f (q*μ.xi2 (q*a)) a := by
    convert (μ.hasDerivAt_xi1 (q*a)).comp a
      ((hasDerivAt_id a).const_mul q) using 1 <;> first | rfl | ring
  have h := ((factor_hasDerivAt a).mul (hf.pow 2)).div_const (μ.xi1 Q)
  change HasDerivAt (sourceMixedGradientReduction μ Q) _ a at h
  rw [h.deriv]
  dsimp [f,q]
  ring

theorem sourceMixedGradientReduction_second (μ : FiniteMixture) (Q a : ℝ) :
    deriv (deriv (sourceMixedGradientReduction μ Q)) a =
      (-2*(μ.xi1 (Real.sqrt Q*a))^2-
        8*a*Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)*μ.xi2 (Real.sqrt Q*a)+
        (1-a^2)*2*(Real.sqrt Q)^2*
          ((μ.xi2 (Real.sqrt Q*a))^2+
            μ.xi1 (Real.sqrt Q*a)*μ.v1 (Real.sqrt Q*a)))/μ.xi1 Q := by
  let q := Real.sqrt Q
  let f : ℝ → ℝ := fun t => μ.xi1 (q*t)
  let g : ℝ → ℝ := fun t => μ.xi2 (q*t)
  have hf : HasDerivAt f (q*μ.xi2 (q*a)) a := by
    convert (μ.hasDerivAt_xi1 (q*a)).comp a
      ((hasDerivAt_id a).const_mul q) using 1 <;> first | rfl | ring
  have hg : HasDerivAt g (q*μ.v1 (q*a)) a := by
    convert (μ.hasDerivAt_xi2 (q*a)).comp a
      ((hasDerivAt_id a).const_mul q) using 1 <;> first | rfl | ring
  have h1 : HasDerivAt (fun t => -2*t*f t^2)
      (-2*f a^2-4*a*f a*q*μ.xi2 (q*a)) a := by
    convert (((hasDerivAt_id a).const_mul (-2)).mul (hf.pow 2)) using 1
    · funext t
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
      ring
  have h2 : HasDerivAt (fun t => (1-t^2)*2*f t*q*g t)
      (-4*a*f a*q*g a+
        (1-a^2)*2*q^2*((g a)^2+f a*μ.v1 (q*a))) a := by
    convert ((((factor_hasDerivAt a).mul_const 2).mul hf).mul_const q).mul hg
      using 1
    dsimp [f,g]
    ring
  have h := (h1.add h2).div_const (μ.xi1 Q)
  have hfun : deriv (sourceMixedGradientReduction μ Q) =
      fun t => (-2*t*(f t)^2+(1-t^2)*2*f t*q*g t)/μ.xi1 Q := by
    funext t
    exact sourceMixedGradientReduction_first μ Q t
  rw [hfun]
  change HasDerivAt (fun t => (-2*t*(f t)^2+(1-t^2)*2*f t*q*g t)/μ.xi1 Q)
    _ a at h
  rw [h.deriv]
  dsimp [f,g,q]
  ring

theorem sourceMixedGradientReduction_second_contact
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    deriv (deriv (sourceMixedGradientReduction μ Q)) (Real.sqrt Q) =
      -2*μ.xi1 Q-8*Q*μ.xi2 Q+
        2*(1-Q)*Q*((μ.xi2 Q)^2/μ.xi1 Q+μ.v1 Q) := by
  rw [sourceMixedGradientReduction_second μ Q,
    Real.mul_self_sqrt hQ.le, Real.sq_sqrt hQ.le]
  have hxi : μ.xi1 Q ≠ 0 := (μ.xi1_pos hQ).ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt hQ.le]
  ring

end
end SlowEquilibration.SphericalTAPMixedGradientSecond
