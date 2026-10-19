-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StrongFieldLaplace

@[expose] public section

/-! Genuine large-radial-shift Gaussian integrals for the crude determinant
bound, with an explicit cutoff and no asymptotic tail hypothesis. -/

namespace SlowEquilibration.StrongFieldComplexity
noncomputable section
open MeasureTheory Set
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def crudeRadialExponent (C A v α h k : ℝ) : ℝ :=
  C+|k|-k^2/(2*A)-(h-α*k)^2/(2*v)

def crudeRadialCutoff (C A : ℝ) : ℝ :=
  4*A+Real.sqrt (8*A*(|C|+1))+1

theorem crudeRadialCutoff_pos (C : ℝ) {A : ℝ} (hA : 0 < A) :
    0 < crudeRadialCutoff C A := by
  unfold crudeRadialCutoff
  positivity

theorem crudeRadialExponent_tail_le (C : ℝ) {A v : ℝ} (hA : 0 < A) (hv : 0 < v)
    (α h k : ℝ) (hk : crudeRadialCutoff C A ≤ |k|) :
    crudeRadialExponent C A v α h k ≤ -1-(1/(8*A))*k^2 := by
  have hs : 0 ≤ Real.sqrt (8*A*(|C|+1)) := Real.sqrt_nonneg _
  have hk4 : 4*A ≤ |k| := by dsimp only [crudeRadialCutoff] at hk; linarith
  have hks : Real.sqrt (8*A*(|C|+1)) ≤ |k| := by dsimp only [crudeRadialCutoff] at hk; linarith
  have hsq : 8*A*(|C|+1) ≤ k^2 := by
    have ht := sq_le_sq₀ hs (abs_nonneg k) |>.mpr hks
    rwa [Real.sq_sqrt (by positivity), sq_abs] at ht
  have hlin : 4*A*|k| ≤ k^2 := by
    have ht := mul_le_mul_of_nonneg_right hk4 (abs_nonneg k)
    nlinarith [sq_abs k]
  have hpen : 0 ≤ (h-α*k)^2/(2*v) := by positivity
  unfold crudeRadialExponent
  have he : C+|k|-k^2/(2*A)-(-1-(1/(8*A))*k^2) =
      (8*A*(C+1)+8*A*|k|-3*k^2)/(8*A) := by field_simp; ring
  apply (sub_nonpos.mp ?_)
  calc
    _ ≤ C+|k|-k^2/(2*A)-(-1-(1/(8*A))*k^2) := by linarith
    _ = _ := he
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith [le_abs_self C]) (by positivity)

/-- The tail integrand is dominated by an actual one-dimensional Gaussian,
with an exponential loss independent of height. -/
theorem crudeRadial_exp_envelope (C : ℝ) {A v N : ℝ} (hA : 0 < A) (hv : 0 < v)
    (hN : 1 ≤ N) (α h k : ℝ) (hk : crudeRadialCutoff C A ≤ |k|) :
    Real.exp (N*crudeRadialExponent C A v α h k) ≤
      Real.exp (-N)*Real.exp (-(1/(8*A))*k^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul_of_nonneg_left (crudeRadialExponent_tail_le C hA hv α h k hk)
    (show 0 ≤ N by linarith)
  have hc : 0 ≤ (1/(8*A))*k^2 := by positivity
  nlinarith

/-- Literal scalar Lebesgue tail integral, including every height in a fixed
finite interval. -/
theorem crudeRadial_lintegral_tail (C L U : ℝ) {A v N : ℝ} (hA : 0 < A) (hv : 0 < v)
    (hN : 1 ≤ N) (α : ℝ) :
    (∫⁻ h in Icc L U, ∫⁻ k in {k : ℝ | crudeRadialCutoff C A ≤ |k|},
      ENNReal.ofReal (Real.exp (N*crudeRadialExponent C A v α h k))) ≤
        ENNReal.ofReal ((|U-L|+1)*Real.sqrt (Real.pi/(1/(8*A)))*Real.exp (-N)) := by
  have hc : 0 < 1/(8*A) := by positivity
  have hgauss : (∫⁻ k : ℝ, ENNReal.ofReal (Real.exp (-(1/(8*A))*k^2)))=
      ENNReal.ofReal (Real.sqrt (Real.pi/(1/(8*A)))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hc)
      (Filter.Eventually.of_forall (fun k => (Real.exp_pos _).le)), integral_gaussian]
  have hpoint (h : ℝ) :
      (∫⁻ k in {k : ℝ | crudeRadialCutoff C A ≤ |k|},
        ENNReal.ofReal (Real.exp (N*crudeRadialExponent C A v α h k))) ≤
          ENNReal.ofReal (Real.exp (-N))*ENNReal.ofReal (Real.sqrt (Real.pi/(1/(8*A)))) := by
    calc
      _ ≤ ∫⁻ k in {k : ℝ | crudeRadialCutoff C A ≤ |k|},
          ENNReal.ofReal (Real.exp (-N))*ENNReal.ofReal (Real.exp (-(1/(8*A))*k^2)) := by
        apply setLIntegral_mono (by fun_prop)
        intro k hk
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (crudeRadial_exp_envelope C hA hv hN α h k hk)
      _ ≤ ∫⁻ k : ℝ, ENNReal.ofReal (Real.exp (-N))*ENNReal.ofReal (Real.exp (-(1/(8*A))*k^2)) :=
        by
          simpa only [Measure.restrict_univ] using
            (lintegral_mono_set (μ := volume) (f := fun k : ℝ =>
              ENNReal.ofReal (Real.exp (-N))*ENNReal.ofReal (Real.exp (-(1/(8*A))*k^2)))
                (subset_univ {k : ℝ | crudeRadialCutoff C A ≤ |k|}))
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hgauss]
  apply (lintegral_mono (fun h => hpoint h)).trans
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-N))*ENNReal.ofReal (Real.sqrt (Real.pi/(1/(8*A))))*
        ENNReal.ofReal (|U-L|+1) := by
      gcongr
      linarith [le_abs_self (U-L)]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
      congr 1
      ring

end
end SlowEquilibration.StrongFieldComplexity
