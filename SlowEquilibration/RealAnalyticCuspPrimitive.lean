-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RealAnalyticCuspNormalForm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

@[expose] public section
noncomputable section
namespace SlowEquilibration.RealAnalyticCuspPrimitive
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integrating a proved derivative bound raises its vanishing order by one. -/
theorem primitive_isBigO {f : ℝ → ℝ} {k : ℕ}
    (hf : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x)
    (hd : deriv f =O[𝓝 (0 : ℝ)] (fun x => x ^ k)) (h0 : f 0 = 0) :
    f =O[𝓝 (0 : ℝ)] (fun x => x ^ (k + 1)) := by
  have hd' : fderiv ℝ f =O[𝓝 (0 : ℝ)] (fun x : ℝ => ‖x - 0‖ ^ (k : ℝ)) := by
    rw [← isBigO_norm_left]
    simpa only [sub_zero,Real.rpow_natCast,← norm_pow,norm_deriv_eq_norm_fderiv]
      using hd.norm_left.norm_right
  have h := isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero
    (by positivity : (0 : ℝ) ≤ k) hf hd' h0
  have hp : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hp] at h
  simpa only [sub_zero,Real.rpow_natCast,← norm_pow,isBigO_norm_right] using h

/-- A concrete second-order remainder from analyticity and the actual derivative. -/
theorem analytic_first_order {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    (fun x : ℝ => f x - f 0 - deriv f 0 * x) =O[𝓝 (0 : ℝ)] (fun x => x ^ 2) := by
  have hD : (fun x : ℝ => deriv f x - deriv f 0) =O[𝓝 (0 : ℝ)] (fun x => x) := by
    simpa only [sub_zero] using hf.deriv.differentiableAt.isBigO_sub
  have he : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt (fun x : ℝ => f x - f 0 - deriv f 0 * x) (deriv f x - deriv f 0) x := by
    filter_upwards [hf.eventually_analyticAt] with x hx
    convert (hx.differentiableAt.hasDerivAt.sub_const (f 0)).sub
      ((hasDerivAt_id x).const_mul (deriv f 0)) using 1 <;> simp [Pi.sub_def]
  apply primitive_isBigO (k := 1) (he.mono (fun x hx => hx.differentiableAt)) ?_ (by simp)
  apply hD.congr' ?_ (Filter.Eventually.of_forall (fun x => (pow_one x).symm))
  exact he.mono (fun x hx => hx.deriv.symm)

/-- An actual derivative factorization, together with its first nonzero
coefficient, yields the integrated cusp coefficient and a full next-order remainder. -/
theorem barrier_from_derivative {B X : ℝ → ℝ} {k : ℕ} {d s : ℝ}
    (hk : 1 ≤ k) (hB : AnalyticAt ℝ B 0) (hB0 : B 0 = 0)
    (hX : (fun x : ℝ => X x - s * x) =O[𝓝 (0 : ℝ)] (fun x => x ^ 2))
    (hd : ∀ᶠ x in 𝓝 (0 : ℝ), deriv B x = d * x ^ (k - 1) * X x) :
    (fun x : ℝ => B x - (d * s / (k + 1 : ℕ)) * x ^ (k + 1))
      =O[𝓝 (0 : ℝ)] (fun x => x ^ (k + 2)) := by
  let C : ℝ := d * s / (k + 1 : ℕ)
  have hc : C * (k + 1 : ℕ) = d * s := by dsimp [C]; field_simp
  have he : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt (fun x : ℝ => B x - C * x ^ (k + 1))
        (d * x ^ (k - 1) * (X x - s * x)) x := by
    filter_upwards [hB.eventually_analyticAt,hd] with x hx hdx
    convert hx.differentiableAt.hasDerivAt.sub
      (((hasDerivAt_id x).pow (k + 1)).const_mul C) using 1
    · rfl
    simp only [hdx, Nat.add_sub_cancel, mul_one]
    rw [← mul_assoc C, hc]
    have hp : x ^ (k - 1) * x = x ^ k := by
      rw [← pow_succ]; congr 1; omega
    simp only [id_eq]
    rw [← hp]
    ring
  have hO := ((isBigO_refl (fun x : ℝ => x ^ (k - 1)) (𝓝 (0 : ℝ))).mul hX).const_mul_left d
  have hder : deriv (fun x : ℝ => B x - C * x ^ (k + 1))
      =O[𝓝 (0 : ℝ)] (fun x => x ^ (k + 1)) := by
    apply hO.congr' ?_ ?_
    · filter_upwards [he] with x hx
      rw [hx.deriv]
      ring
    · exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [← pow_add]; congr 1; omega)
  simpa only [Nat.add_assoc,show (1 : ℕ) + 1 = 2 by rfl] using
    primitive_isBigO (he.mono (fun x hx => hx.differentiableAt)) hder (by simp [hB0])

end SlowEquilibration.RealAnalyticCuspPrimitive
