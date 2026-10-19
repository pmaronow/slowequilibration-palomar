module
public import FourPapersCommon.MixtureAnalysis

@[expose] public section

/-! Uniform derivative bounds and absolute summability of interaction amplitudes. -/
noncomputable section
open Set
namespace FourPapersCommon.AdmissibleEvenMixture

theorem first_nonneg (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : 0≤q) : 0≤ξ.first q := by
  unfold first
  exact tsum_nonneg (fun p=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ξ.nonneg p))
    (pow_nonneg hq _))

theorem second_le_at_one (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|≤1) :
    ξ.second q≤ξ.second 1 := by
  unfold second
  apply Summable.tsum_le_tsum _ (ξ.summable_second hq) (ξ.summable_second (by norm_num))
  intro p
  have hp : q^(p-2)≤1 := (le_abs_self _).trans
    (by simpa only [abs_pow] using pow_le_one₀ (abs_nonneg q) hq (n:=p-2))
  simpa only [one_pow,mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p))

theorem abs_second_le_at_one (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|≤1) :
    |ξ.second q|≤ξ.second 1 := by
  rw [abs_of_nonneg (ξ.second_nonneg q)]
  exact ξ.second_le_at_one hq

theorem summable_amplitude (ξ : AdmissibleEvenMixture) :
    Summable (fun p=>Real.sqrt (ξ.coefficient p)) := by
  have hgeo : Summable (fun p:ℕ=>(1/2:ℝ)^p) := summable_geometric_of_abs_lt_one (by norm_num)
  apply (ξ.summable.add hgeo).of_nonneg_of_le (fun p=>Real.sqrt_nonneg _)
  intro p
  have hw : 0<(2:ℝ)^p := by positivity
  have hr : 0≤(1/2:ℝ)^p := by positivity
  have he : (2:ℝ)^p*(1/2:ℝ)^p=1 := by rw [←mul_pow];norm_num
  have hs := mul_nonneg hw.le (sq_nonneg (Real.sqrt (ξ.coefficient p)-(1/2:ℝ)^p))
  have hh := Real.sq_sqrt (ξ.nonneg p)
  nlinarith [Real.sqrt_nonneg (ξ.coefficient p)]

end FourPapersCommon.AdmissibleEvenMixture
