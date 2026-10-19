-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiShiftedGaussianTrial
public import SlowEquilibration.SphericalGuerraBound
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

/-! Fractional Jensen bounds for the actual finite iid Gaussian row bank.
No random-energy limit or pressure conclusion is supplied as a hypothesis.
The common Gaussian field is retained as a deterministic parameter before
its independent Gaussian average is taken. -/

namespace SlowEquilibration.SphericalParisiGaussianREMJensen
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalParisiShiftedGaussianTrial
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem rpow_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s,0 ≤ f i) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    (∑ i ∈ s,f i)^m ≤ ∑ i ∈ s,(f i)^m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hm.ne']
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow (hf i (by simp))
      (Finset.sum_nonneg (fun j hj => hf j (by simp [hj]))) hm.le hm1).trans
      (add_le_add le_rfl (ih (fun j hj => hf j (by simp [hj]))))

def logAverageExp (k : ℕ) (f : Fin k → ℝ) : ℝ :=
  Real.log ((∑ i : Fin k,Real.exp (f i))/(k : ℝ))

private theorem sum_exp_pos (k : ℕ) (hk : 0 < k) (f : Fin k → ℝ) :
    0 < ∑ i : Fin k,Real.exp (f i) := by
  let i : Fin k := ⟨0,hk⟩
  exact (Real.exp_pos (f i)).trans_le (Finset.single_le_sum
    (fun j _ => (Real.exp_pos (f j)).le) (Finset.mem_univ i))

theorem logAverageExp_nonnegative (k : ℕ) (hk : 0 < k)
    (f : Fin k → ℝ) (hf : ∀ i,0 ≤ f i) : 0 ≤ logAverageExp k f := by
  apply Real.log_nonneg
  have hc : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hc).mpr
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Real.one_le_exp_iff.mpr (hf i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] using h

/-- Literal finite-label fractional-power inequality, including its label
entropy term. This is deterministic and uses no limit theorem. -/
theorem logAverageExp_fractional_bound (k : ℕ) (hk : 0 < k)
    (f : Fin k → ℝ) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    logAverageExp k f ≤ logAverageExp k (fun i => m*f i)/m+
      (1-m)*Real.log (k : ℝ)/m := by
  have hc : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hpow := rpow_sum_le Finset.univ (fun i => Real.exp (f i))
    (fun i _ => (Real.exp_pos _).le) hm hm1
  simp_rw [← Real.exp_mul,mul_comm (f _) m] at hpow
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (sum_exp_pos k hk f) m) hpow
  rw [Real.log_rpow (sum_exp_pos k hk f)] at hlog
  unfold logAverageExp
  rw [Real.log_div (sum_exp_pos k hk f).ne' hc.ne',
    Real.log_div (sum_exp_pos k hk (fun i => m*f i)).ne' hc.ne']
  rw [← add_div]
  apply (le_div_iff₀ hm).mpr
  nlinarith [hlog]

/-- Log Jensen derived directly from the actual positive integral and the
logarithm's tangent inequality. -/
theorem integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hl : Integrable (fun w => Real.log (f w)) μ)
    (hp : ∀ᵐ w ∂μ,0 < f w) :
    (∫ w,Real.log (f w) ∂μ) ≤ Real.log (∫ w,f w ∂μ) := by
  have hi : 0 < ∫ w,f w ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h => h.le)) hf).mpr (by
      have hs : Function.support f =ᵐ[μ] univ := hp.mono (fun w hw => by
        apply propext
        change f w ≠ 0 ↔ True
        exact ⟨fun _ => trivial,fun _ => hw.ne'⟩)
      rw [measure_congr hs]
      simp)
  have ht : ∀ᵐ w ∂μ,Real.log (f w) ≤
      f w/(∫ z,f z ∂μ)-1+Real.log (∫ z,f z ∂μ) := by
    filter_upwards [hp] with w hw
    have h := Real.log_le_sub_one_of_pos (div_pos hw hi)
    rw [Real.log_div hw.ne' hi.ne'] at h
    linarith
  have hb := integral_mono_ae hl
    (((hf.div_const _).sub (integrable_const (1 : ℝ))).add (integrable_const _)) ht
  have he : (∫ w,f w/(∫ z,f z ∂μ)-1+Real.log (∫ z,f z ∂μ) ∂μ)=
      Real.log (∫ z,f z ∂μ) := by
    rw [integral_add (f := fun w => f w/(∫ z,f z ∂μ)-1)
      (g := fun _ => Real.log (∫ z,f z ∂μ))
      ((hf.div_const _).sub (integrable_const (1 : ℝ))) (integrable_const _),
      integral_sub (f := fun w => f w/(∫ z,f z ∂μ)) (g := fun _ => (1 : ℝ))
      (hf.div_const _) (integrable_const (1 : ℝ)),integral_div]
    simp only [integral_const,probReal_univ,one_smul,div_self hi.ne',sub_self,zero_add]
  exact hb.trans_eq he

private theorem expAverage_one_le (k : ℕ) (hk : 0 < k)
    (f : Fin k → ℝ) (hf : ∀ i,0 ≤ f i) :
    1 ≤ (∑ i : Fin k,Real.exp (f i))/(k : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Real.one_le_exp_iff.mpr (hf i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_mul] using h

/-- A genuine finite probability Jensen consumer. Its assumptions concern
only the actual row exponential integrals, not the desired logarithmic bound. -/
theorem expected_logAverageExp_fractional_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k)
    (f : Ω → Fin k → ℝ) (hf : ∀ i,Measurable (fun w => f w i))
    (hn : ∀ w i,0 ≤ f w i) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (he : ∀ i,Integrable (fun w => Real.exp (m*f w i)) μ) :
    Integrable (fun w => logAverageExp k (f w)) μ ∧
      (∫ w,logAverageExp k (f w) ∂μ) ≤
        Real.log ((∑ i : Fin k,∫ w,Real.exp (m*f w i) ∂μ)/(k : ℝ))/m+
        (1-m)*Real.log (k : ℝ)/m := by
  let V := fun w => (∑ i : Fin k,Real.exp (m*f w i))/(k : ℝ)
  have hiV : Integrable V μ := (integrable_finsetSum Finset.univ (fun i _ => he i)).div_const _
  have hV : ∀ w,1 ≤ V w := fun w => expAverage_one_le k hk _
    (fun i => mul_nonneg hm.le (hn w i))
  have hlogV : Integrable (fun w => Real.log (V w)) μ := by
    apply hiV.mono' (hiV.aestronglyMeasurable.aemeasurable.log.aestronglyMeasurable)
    exact .of_forall fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (hV w))]
      exact Real.log_le_self (lt_of_lt_of_le zero_lt_one (hV w)).le
  have hH : Integrable (fun w => Real.log (V w)/m+(1-m)*Real.log (k : ℝ)/m) μ :=
    (hlogV.div_const _).add (integrable_const _)
  have hmf : Measurable (fun w => logAverageExp k (f w)) := by
    unfold logAverageExp
    exact (Finset.measurable_sum Finset.univ (fun i _ => (hf i).exp)).div_const _ |>.log
  have hi : Integrable (fun w => logAverageExp k (f w)) μ := by
    apply hH.mono' hmf.aestronglyMeasurable
    exact .of_forall fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (logAverageExp_nonnegative k hk (f w) (hn w))]
      exact logAverageExp_fractional_bound k hk (f w) hm hm1
  refine ⟨hi,?_⟩
  have hb := integral_mono hi hH (fun w => logAverageExp_fractional_bound k hk (f w) hm hm1)
  rw [integral_add (hlogV.div_const _) (integrable_const _),integral_div] at hb
  simp only [integral_const,probReal_univ,one_smul] at hb
  have hj := integral_log_le_log_integral hiV hlogV
    (.of_forall fun w => lt_of_lt_of_le zero_lt_one (hV w))
  have heV : (∫ w,V w ∂μ)=(∑ i : Fin k,∫ w,Real.exp (m*f w i) ∂μ)/(k : ℝ) := by
    rw [show V=(fun w => (∑ i : Fin k,Real.exp (m*f w i))/(k : ℝ)) by rfl,
      integral_div,integral_finsetSum Finset.univ (fun i _ => he i)]
  rw [heV] at hj
  exact hb.trans (add_le_add (div_le_div_of_nonneg_right hj hm.le) le_rfl)

def gaussianRow (N k : ℕ) (i : Fin k) :
    EuclideanSpace ℝ (Fin k × Fin N) → EuclideanSpace ℝ (Fin N) :=
  projectGaussian (fun j => (i,j))

theorem gaussianRow_hasLaw (N k : ℕ) (i : Fin k) :
    HasLaw (gaussianRow N k i) (stdGaussian (EuclideanSpace ℝ (Fin N)))
      (SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) := by
  rw [show stdGaussian (EuclideanSpace ℝ (Fin N))=
    SYK.standardGaussianMeasureOnEuclidean (Fin N) by
      rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]]
  exact projectGaussian_hasLaw _ (fun j l h => congrArg Prod.snd h)

def actualGaussianNormLogAverage {N k : ℕ}
    (h : EuclideanSpace ℝ (Fin N)) (a ell : ℝ)
    (g : EuclideanSpace ℝ (Fin k × Fin N)) : ℝ :=
  logAverageExp k (fun i => ell*‖h+Real.sqrt a • gaussianRow N k i g‖)

/-- The true finite iid row-bank endpoint, with exact fractional label cost.
The shifted Gaussian moment on the right is its actual Gaussian integral. -/
theorem actual_gaussian_norm_log_average_upper {N k : ℕ} (hk : 0 < k)
    (h : EuclideanSpace ℝ (Fin N)) {a ell m b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hm : 0 < m) (hm1 : m ≤ 1)
    (hb : 0 < b) (hmargin : 0 < b-(m*ell)*a) :
    Integrable (actualGaussianNormLogAverage h a ell)
      (SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) ∧
      (∫ g,actualGaussianNormLogAverage h a ell g
        ∂SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) ≤
        Real.log (shiftedNormMoment h a (m*ell))/m+(1-m)*Real.log (k : ℝ)/m := by
  have hi := shiftedNormMoment_integrable h ha (mul_nonneg hm.le hEll) hb hmargin
  have he (i : Fin k) : Integrable (fun g =>
      Real.exp (m*(ell*‖h+Real.sqrt a • gaussianRow N k i g‖)))
      (SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) := by
    simpa only [Function.comp_def,mul_assoc] using (gaussianRow_hasLaw N k i).integrable_comp hi
  have hmean (i : Fin k) : (∫ g,Real.exp (m*(ell*‖h+Real.sqrt a • gaussianRow N k i g‖))
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N))=shiftedNormMoment h a (m*ell) := by
    simpa only [Function.comp_def,mul_assoc,shiftedNormMoment] using
      (gaussianRow_hasLaw N k i).integral_comp hi.aestronglyMeasurable
  have hf (i : Fin k) : Measurable (fun g => ell*‖h+Real.sqrt a • gaussianRow N k i g‖) := by
    exact measurable_const.mul ((measurable_const.add
      ((projectGaussian_measurable (fun j : Fin N => (i,j))).const_smul (Real.sqrt a))).norm)
  have H := expected_logAverageExp_fractional_bound k hk
    (fun g i => ell*‖h+Real.sqrt a • gaussianRow N k i g‖) hf
    (fun g i => mul_nonneg hEll (norm_nonneg _)) hm hm1 he
  simp only [hmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_div_cancel_left₀ _ (show (k : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hk.ne')] at H
  exact H


/-- Explicit finite-dimensional determinant bound for the actual row bank.
It keeps the true common-field squared norm and actual finite label cost. -/
theorem actual_gaussian_norm_log_average_quadratic_upper {N k : ℕ} (hk : 0 < k)
    (h : EuclideanSpace ℝ (Fin N)) {a ell m b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hm : 0 < m) (hm1 : m ≤ 1)
    (hb : 0 < b) (hmargin : 0 < b-(m*ell)*a) :
    (∫ g,actualGaussianNormLogAverage h a ell g
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) ≤
      -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+
        ell*b/2+ell*‖h‖^2/(2*(b-(m*ell)*a))+
        (1-m)*Real.log (k : ℝ)/m := by
  have H := (actual_gaussian_norm_log_average_upper hk h ha hEll hm hm1 hb hmargin).2
  have D := log_shiftedNormMoment_le h ha (mul_nonneg hm.le hEll) hb hmargin
  rw [finrank_euclideanSpace,Fintype.card_fin] at D
  apply H.trans
  have hd := add_le_add (div_le_div_of_nonneg_right D hm.le)
    (le_refl ((1-m)*Real.log (k : ℝ)/m))
  apply hd.trans_eq
  field_simp

end
end SlowEquilibration.SphericalParisiGaussianREMJensen
