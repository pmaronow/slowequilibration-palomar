-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGibbs
public import SlowEquilibration.SphericalEnergy

/-! The original uniform sphere start is the literal inverse Gibbs
density, and its actual entropy has the source linear energy-envelope
bound. No initial-density or entropy estimate is assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel SphericalAging.HardSphereDynamics
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def uniformInitialDensity (N : ℕ) (β : ℝ) (H : Vector N → ℝ) (x : Vector N) : ℝ :=
  partition N β H*Real.exp (-β*H x)

theorem uniformInitialDensity_continuous (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H) :
    Continuous (uniformInitialDensity N β H) :=
  (Real.continuous_exp.comp (continuous_const.mul hH)).const_mul _

theorem uniformInitialDensity_pos (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (x : Vector N) : 0 < uniformInitialDensity N β H x :=
  mul_pos (partition_pos hN β hH) (Real.exp_pos _)

theorem uniformInitialDensity_change (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) :
    (∫ x,uniformInitialDensity N β H x*f x ∂gibbsLaw N β H)=∫ x,f x ∂sphereLaw N := by
  rw [integral_gibbsLaw hN β hH]
  apply integral_congr_ae
  exact .of_forall (fun x => by
    dsimp only [gibbsDensity,uniformInitialDensity]
    have hz := (partition_pos hN β hH).ne'
    have he : Real.exp (β*H x)*Real.exp (-β*H x)=1 := by
      rw [← Real.exp_add]
      rw [show β*H x+-β*H x=0 by ring,Real.exp_zero]
    calc
      _ = (Real.exp (β*H x)*Real.exp (-β*H x))*f x := by field_simp [hz]
      _ = f x := by rw [he,one_mul])

theorem uniformInitialDensity_integral (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : (∫ x,uniformInitialDensity N β H x ∂gibbsLaw N β H)=1 := by
  simpa only [mul_one,integral_const,probReal_univ,one_smul] using
    uniformInitialDensity_change hN β H hH (fun _ => 1)

theorem uniformInitialDensity_le (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (H : Vector N → ℝ) (hH : Continuous H) (B : ℝ)
    (hB : ∀ x,OnSphere x → |H x| ≤ B) (x : Vector N) (hx : OnSphere x) :
    uniformInitialDensity N β H x ≤ Real.exp (2*β*B) := by
  have hZ : partition N β H ≤ Real.exp (β*B) := by
    have hi := integral_mono_ae (partition_integrand_integrable hN β hH)
      (integrable_const (Real.exp (β*B))) (by
        filter_upwards [sphereLaw_support hN] with y hy
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left ((le_abs_self (H y)).trans
          (hB y ((onSphere_iff_norm_sq y).mpr hy))) hβ)
    simpa only [partition,integral_const,probReal_univ,one_smul] using hi
  have hxexp : Real.exp (-β*H x) ≤ Real.exp (β*B) := by
    apply Real.exp_le_exp.mpr
    have hb := (abs_le.mp (hB x hx)).1
    nlinarith
  change partition N β H*Real.exp (-β*H x) ≤ _
  calc
    _ ≤ Real.exp (β*B)*Real.exp (β*B) :=
      mul_le_mul hZ hxexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add];congr 1;ring

/-- Actual source initial entropy: the energy envelope enters only through
its logarithm and gives a linear bound in B. -/
theorem uniformInitialDensity_entropy_le (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (H : Vector N → ℝ) (hH : Continuous H) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x,OnSphere x → |H x| ≤ B) :
    (∫ x,(1+uniformInitialDensity N β H x)*Real.log (1+uniformInitialDensity N β H x)
      ∂gibbsLaw N β H) ≤ 2*Real.log 2+4*β*B := by
  let := gibbsLaw_probability hN β hH
  let F := fun x => 1+uniformInitialDensity N β H x
  have hFc : Continuous F := continuous_const.add (uniformInitialDensity_continuous β H hH)
  have hFp (x : Vector N) : 0 < F x := by
    dsimp [F]
    linarith [uniformInitialDensity_pos hN β H hH x]
  have hLog : Continuous (fun x => Real.log (F x)) := hFc.log (fun x => (hFp x).ne')
  have hFi := integrable_gibbs_of_continuous hN β hH hFc
  have hEi := integrable_gibbs_of_continuous hN β hH (hFc.mul hLog)
  have hFmean : (∫ x,F x ∂gibbsLaw N β H)=2 := by
    change (∫ x,1+uniformInitialDensity N β H x ∂gibbsLaw N β H)=2
    rw [integral_add (integrable_const (1 : ℝ))
      (integrable_gibbs_of_continuous hN β hH (uniformInitialDensity_continuous β H hH))]
    simp only [integral_const,probReal_univ,one_smul,uniformInitialDensity_integral hN β H hH]
    norm_num
  have hlogBound : Real.log (1+Real.exp (2*β*B)) ≤ Real.log 2+2*β*B := by
    have he : 1 ≤ Real.exp (2*β*B) := Real.one_le_exp_iff.mpr (by positivity)
    have hm := Real.log_le_log (by positivity : 0 < 1+Real.exp (2*β*B))
      (show 1+Real.exp (2*β*B) ≤ 2*Real.exp (2*β*B) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp] at hm
    exact hm
  have hbound : (∫ x,F x*Real.log (F x) ∂gibbsLaw N β H) ≤
      Real.log (1+Real.exp (2*β*B))*2 := by
    have hi := integral_mono_ae hEi (hFi.const_mul (Real.log (1+Real.exp (2*β*B)))) (by
      filter_upwards [gibbsLaw_support hN β H] with x hx
      have hb := uniformInitialDensity_le hN β hβ H hH B hB x ((onSphere_iff_norm_sq x).mpr hx)
      have hl : Real.log (F x) ≤ Real.log (1+Real.exp (2*β*B)) :=
        Real.log_le_log (hFp x) (by dsimp [F]; linarith)
      exact (mul_le_mul_of_nonneg_left hl (hFp x).le).trans_eq (mul_comm _ _))
    exact hi.trans_eq (by rw [integral_const_mul,hFmean])
  exact hbound.trans (by nlinarith [hlogBound])

end SlowEquilibration.SphericalForm
