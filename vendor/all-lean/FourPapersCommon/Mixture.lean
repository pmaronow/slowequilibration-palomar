module
public import Mathlib

@[expose] public section

/-! The actual exponentially summable even covariance mixtures. The
coefficient at order p is b_p squared, and inactive orders have value zero. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon

structure AdmissibleEvenMixture where
  coefficient : ℕ → ℝ
  nonneg : ∀ p, 0 ≤ coefficient p
  active_even : ∀ p, coefficient p ≠ 0 → 2 ≤ p ∧ Even p
  nonzero : ∃ p, 0 < coefficient p
  summable : Summable (fun p => (2:ℝ)^p*coefficient p)

namespace AdmissibleEvenMixture

def value (ξ : AdmissibleEvenMixture) (q : ℝ) : ℝ :=
  ∑' (p:ℕ), ξ.coefficient p*q^p

def first (ξ : AdmissibleEvenMixture) (q : ℝ) : ℝ :=
  ∑' (p:ℕ), (p:ℝ)*ξ.coefficient p*q^(p-1)

def second (ξ : AdmissibleEvenMixture) (q : ℝ) : ℝ :=
  ∑' (p:ℕ), (p:ℝ)*(p-1:ℕ)*ξ.coefficient p*q^(p-2)

def variance (ξ : AdmissibleEvenMixture) : ℝ := ξ.first 1
def clock (ξ : AdmissibleEvenMixture) (q : ℝ) : ℝ := ξ.first q/ξ.variance

@[simp] theorem coefficient_zero (ξ : AdmissibleEvenMixture) : ξ.coefficient 0=0 := by
  by_contra h
  have hh := (ξ.active_even 0 h).1
  omega

@[simp] theorem coefficient_one (ξ : AdmissibleEvenMixture) : ξ.coefficient 1=0 := by
  by_contra h
  have hh := (ξ.active_even 1 h).1
  omega

theorem summable_coefficient (ξ : AdmissibleEvenMixture) : Summable ξ.coefficient := by
  apply ξ.summable.of_nonneg_of_le ξ.nonneg
  intro p
  exact le_mul_of_one_le_left (ξ.nonneg p) (one_le_pow₀ (by norm_num))

theorem summable_first_coefficient (ξ : AdmissibleEvenMixture) :
    Summable (fun (p:ℕ) => (p:ℝ)*ξ.coefficient p) := by
  apply ξ.summable.of_nonneg_of_le (fun p=>mul_nonneg (Nat.cast_nonneg _) (ξ.nonneg p))
  intro p
  apply mul_le_mul_of_nonneg_right _ (ξ.nonneg p)
  exact_mod_cast p.lt_two_pow_self.le

theorem summable_value (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|≤1) :
    Summable (fun p=>ξ.coefficient p*q^p) := by
  apply Summable.of_norm_bounded ξ.summable
  intro p
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),abs_pow]
  have hp : |q|^p≤1 := pow_le_one₀ (abs_nonneg _) hq
  calc
    ξ.coefficient p*|q|^p≤ξ.coefficient p*1 :=
      mul_le_mul_of_nonneg_left hp (ξ.nonneg p)
    _ ≤ (2:ℝ)^p*ξ.coefficient p := by
      simpa only [mul_one] using
        le_mul_of_one_le_left (ξ.nonneg p) (one_le_pow₀ (by norm_num))

theorem summable_first (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|≤1) :
    Summable (fun (p:ℕ)=>(p:ℝ)*ξ.coefficient p*q^(p-1)) := by
  apply Summable.of_norm_bounded ξ.summable_first_coefficient
  intro p
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
    abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p),abs_pow]
  have hp : |q|^(p-1)≤1 := pow_le_one₀ (abs_nonneg _) hq
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hp (mul_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p) (ξ.nonneg p))

@[simp] theorem value_zero (ξ : AdmissibleEvenMixture) : ξ.value 0=0 := by
  unfold value
  have he : (fun p:ℕ=>ξ.coefficient p*(0:ℝ)^p)=fun _=>0 := by
    funext p
    rcases eq_or_ne p 0 with rfl|hp
    · simp
    · simp [zero_pow hp]
  rw [he]
  simp

@[simp] theorem first_zero (ξ : AdmissibleEvenMixture) : ξ.first 0=0 := by
  unfold first
  have he : (fun p:ℕ=>(p:ℝ)*ξ.coefficient p*(0:ℝ)^(p-1))=fun _=>0 := by
    funext p
    by_cases hp : ξ.coefficient p=0
    · simp [hp]
    · have hdeg := (ξ.active_even p hp).1
      have hn : p-1≠0 := by omega
      simp [zero_pow hn]
  rw [he]
  simp

theorem value_even (ξ : AdmissibleEvenMixture) (q : ℝ) : ξ.value (-q)=ξ.value q := by
  unfold value
  apply tsum_congr
  intro p
  by_cases hp : ξ.coefficient p=0
  · simp [hp]
  · rw [(ξ.active_even p hp).2.neg_pow]

theorem first_odd (ξ : AdmissibleEvenMixture) (q : ℝ) : ξ.first (-q)= -ξ.first q := by
  unfold first
  rw [←tsum_neg]
  apply tsum_congr
  intro p
  by_cases hp : ξ.coefficient p=0
  · simp [hp]
  · have hdeg := ξ.active_even p hp
    have ho : Odd (p-1) := Nat.Even.sub_odd (by omega) hdeg.2 (by decide : Odd 1)
    rw [ho.neg_pow]
    ring

theorem first_strictMonoOn (ξ : AdmissibleEvenMixture) :
    StrictMonoOn ξ.first (Icc (-1:ℝ) 1) := by
  intro x hx y hy hxy
  rcases ξ.nonzero with ⟨p,hp⟩
  have hdeg := ξ.active_even p hp.ne'
  have hod : Odd (p-1) := Nat.Even.sub_odd (by omega) hdeg.2 (by decide : Odd 1)
  have hpos : 0<(p:ℝ)*ξ.coefficient p := mul_pos (by exact_mod_cast (by omega : 0<p)) hp
  unfold first
  apply Summable.tsum_lt_tsum (i:=p)
  · intro n
    by_cases hn : ξ.coefficient n=0
    · simp [hn]
    · have hh := ξ.active_even n hn
      have ho : Odd (n-1) := Nat.Even.sub_odd (by omega) hh.2 (by decide : Odd 1)
      exact mul_le_mul_of_nonneg_left ((Odd.strictMono_pow ho hxy).le)
        (mul_nonneg (Nat.cast_nonneg _) (ξ.nonneg n))
  · exact mul_lt_mul_of_pos_left (Odd.strictMono_pow hod hxy) hpos
  · exact ξ.summable_first (abs_le.mpr hx)
  · exact ξ.summable_first (abs_le.mpr hy)

theorem variance_pos (ξ : AdmissibleEvenMixture) : 0<ξ.variance := by
  have hh := ξ.first_strictMonoOn (show (0:ℝ)∈Icc (-1:ℝ) 1 by norm_num)
    (show (1:ℝ)∈Icc (-1:ℝ) 1 by norm_num) (by norm_num : (0:ℝ)<1)
  simpa only [first_zero,variance] using hh

@[simp] theorem clock_zero (ξ : AdmissibleEvenMixture) : ξ.clock 0=0 := by
  simp [clock]

@[simp] theorem clock_one (ξ : AdmissibleEvenMixture) : ξ.clock 1=1 := by
  exact div_self ξ.variance_pos.ne'

theorem clock_strictMonoOn (ξ : AdmissibleEvenMixture) :
    StrictMonoOn ξ.clock (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  exact div_lt_div_of_pos_right
    (ξ.first_strictMonoOn ⟨by linarith [hx.1],hx.2⟩ ⟨by linarith [hy.1],hy.2⟩ hxy)
    ξ.variance_pos

theorem continuousOn_value (ξ : AdmissibleEvenMixture) :
    ContinuousOn ξ.value (Icc (-1:ℝ) 1) := by
  apply continuousOn_tsum (fun p=>by fun_prop) ξ.summable_coefficient
  intro p q hq
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),abs_pow]
  have hp : |q|^p≤1 := pow_le_one₀ (abs_nonneg _) (abs_le.mpr hq)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (ξ.nonneg p)

theorem continuousOn_first (ξ : AdmissibleEvenMixture) :
    ContinuousOn ξ.first (Icc (-1:ℝ) 1) := by
  apply continuousOn_tsum (fun p=>by fun_prop) ξ.summable_first_coefficient
  intro p q hq
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
    abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p),abs_pow]
  have hp : |q|^(p-1)≤1 := pow_le_one₀ (abs_nonneg _) (abs_le.mpr hq)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p) (ξ.nonneg p))

theorem continuousOn_clock (ξ : AdmissibleEvenMixture) :
    ContinuousOn ξ.clock (Icc (0:ℝ) 1) :=
  (ξ.continuousOn_first.mono (by intro q hq;exact ⟨by linarith [hq.1],hq.2⟩)).div_const _

theorem clock_mem_unitInterval (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) : ξ.clock q∈Icc (0:ℝ) 1 := by
  have hm := ξ.clock_strictMonoOn.monotoneOn
  constructor
  · simpa using hm (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hq hq.1
  · simpa using hm hq (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) hq.2

theorem image_clock_unitInterval (ξ : AdmissibleEvenMixture) :
    ξ.clock '' Icc (0:ℝ) 1=Icc (0:ℝ) 1 := by
  simpa using ξ.continuousOn_clock.image_Icc_of_monotoneOn
    (by norm_num : (0:ℝ)≤1) ξ.clock_strictMonoOn.monotoneOn

def unitClock (ξ : AdmissibleEvenMixture) (q : Icc (0:ℝ) 1) : Icc (0:ℝ) 1 :=
  ⟨ξ.clock q,ξ.clock_mem_unitInterval q.property⟩

theorem strictMono_unitClock (ξ : AdmissibleEvenMixture) : StrictMono ξ.unitClock := by
  intro x y hxy
  exact ξ.clock_strictMonoOn x.property y.property hxy

theorem surjective_unitClock (ξ : AdmissibleEvenMixture) : Function.Surjective ξ.unitClock := by
  intro y
  have hy : (y:ℝ)∈ξ.clock '' Icc (0:ℝ) 1 := by
    rw [ξ.image_clock_unitInterval]
    exact y.property
  rcases hy with ⟨x,hx,hxy⟩
  exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩

def clockOrderIso (ξ : AdmissibleEvenMixture) : Icc (0:ℝ) 1≃o Icc (0:ℝ) 1 :=
  StrictMono.orderIsoOfSurjective ξ.unitClock ξ.strictMono_unitClock ξ.surjective_unitClock

@[simp] theorem clockOrderIso_apply (ξ : AdmissibleEvenMixture) (q : Icc (0:ℝ) 1) :
    (ξ.clockOrderIso q:ℝ)=ξ.clock q := rfl

theorem continuous_unitClock (ξ : AdmissibleEvenMixture) : Continuous ξ.unitClock :=
  (continuousOn_iff_continuous_domRestrict.mp ξ.continuousOn_clock).subtype_mk _

theorem continuous_clockOrderIso_symm (ξ : AdmissibleEvenMixture) :
    Continuous ξ.clockOrderIso.symm := ξ.clockOrderIso.symm.continuous

end AdmissibleEvenMixture
end FourPapersCommon
