module
public import FourPapersCommon.Mixture

@[expose] public section

/-! Genuine analytic regularity and derivative identities for the covariance series. -/
noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal ContDiff
namespace FourPapersCommon.AdmissibleEvenMixture

private theorem degree_bound (p : ℕ) : (p:ℝ) ≤ 5*(6/5:ℝ)^p := by
  have hh := one_add_mul_le_pow (by norm_num : (-2:ℝ)≤1/5) p
  norm_num at hh
  linarith

private theorem degree_sq_power_bound (p : ℕ) :
    (p:ℝ)^2*(5/4:ℝ)^p ≤ 25*(2:ℝ)^p := by
  have hp := degree_bound p
  have hpp : (p:ℝ)^2 ≤ (5*(6/5:ℝ)^p)^2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hp 2
  calc
    (p:ℝ)^2*(5/4:ℝ)^p ≤ (5*(6/5:ℝ)^p)^2*(5/4:ℝ)^p :=
      mul_le_mul_of_nonneg_right hpp (by positivity)
    _ = 25*(9/5:ℝ)^p := by
      rw [mul_pow, ←pow_mul, Nat.mul_comm p 2, pow_mul,mul_assoc,←mul_pow]
      norm_num
    _ ≤ 25*(2:ℝ)^p := by gcongr; norm_num

private theorem degree_power_bound (p : ℕ) :
    (p:ℝ)*(5/4:ℝ)^p ≤ 25*(2:ℝ)^p := by
  calc
    (p:ℝ)*(5/4:ℝ)^p ≤ (5*(6/5:ℝ)^p)*(5/4:ℝ)^p :=
      mul_le_mul_of_nonneg_right (degree_bound p) (by positivity)
    _ = 5*(3/2:ℝ)^p := by rw [mul_assoc,←mul_pow];norm_num
    _ ≤ 25*(2:ℝ)^p := by
      have hh : (3/2:ℝ)^p≤(2:ℝ)^p := by gcongr;norm_num
      have hp : 0≤(2:ℝ)^p := by positivity
      nlinarith

theorem summable_second_coefficient (ξ : AdmissibleEvenMixture) :
    Summable (fun (p:ℕ)=>(p:ℝ)*(p-1:ℕ)*ξ.coefficient p) := by
  apply (ξ.summable.mul_left 25).of_nonneg_of_le
  · intro p
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p)
  · intro p
    have hp : (p-1:ℕ)≤p := Nat.sub_le _ _
    have hp' : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast hp
    have hb := degree_sq_power_bound p
    have hpow : 1≤(5/4:ℝ)^p := one_le_pow₀ (by norm_num)
    have hpc : 0≤(p:ℝ)^2 := sq_nonneg _
    have hh : (p:ℝ)*(p-1:ℕ) ≤ 25*(2:ℝ)^p := by
      calc
        (p:ℝ)*(p-1:ℕ)≤(p:ℝ)^2 := by
          nlinarith [show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p]
        _≤(p:ℝ)^2*(5/4:ℝ)^p := le_mul_of_one_le_right hpc hpow
        _≤_ := hb
    nlinarith [ξ.nonneg p]

theorem summable_second (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|≤1) :
    Summable (fun (p:ℕ)=>(p:ℝ)*(p-1:ℕ)*ξ.coefficient p*q^(p-2)) := by
  apply Summable.of_norm_bounded ξ.summable_second_coefficient
  intro p
  have hp : |q|^(p-2)≤1 := pow_le_one₀ (abs_nonneg _) hq
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
    abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (show (0:ℝ)≤(p-1:ℕ) from Nat.cast_nonneg _),abs_pow]
  simpa using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p))

theorem hasDerivAt_value (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q|<5/4) : HasDerivAt ξ.value (ξ.first q) q := by
  unfold value first
  apply hasDerivAt_tsum_of_isPreconnected (ξ.summable.mul_left 25)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (t:=Ioo (-(5/4):ℝ) (5/4)) (y₀:=0) (y:=q)
      (g:=fun p y=>ξ.coefficient p*y^p)
      (g':=fun (p:ℕ) y=>(p:ℝ)*ξ.coefficient p*y^(p-1))
  · intro p y hy
    convert ((hasDerivAt_id y).pow p).const_mul (ξ.coefficient p) using 1
    · simp only [id_eq,Pi.pow_apply]
    · simp only [id_eq];ring
  · intro p y hy
    have hay : |y|≤5/4 := (abs_le.mpr ⟨hy.1.le,hy.2.le⟩)
    have hpow : |y|^(p-1)≤(5/4:ℝ)^p := by
      calc
        _≤(5/4:ℝ)^(p-1) := pow_le_pow_left₀ (abs_nonneg _) hay _
        _≤(5/4:ℝ)^p := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
      abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg _),abs_pow]
    have hb := degree_power_bound p
    have hn := ξ.nonneg p
    calc
      (p:ℝ)*ξ.coefficient p*|y|^(p-1)≤(p:ℝ)*ξ.coefficient p*(5/4:ℝ)^p := by gcongr
      _≤25*((2:ℝ)^p*ξ.coefficient p) := by nlinarith
  · norm_num
  · exact ξ.summable_value (by norm_num)
  · exact abs_lt.mp hq

theorem hasDerivAt_first (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q|<5/4) : HasDerivAt ξ.first (ξ.second q) q := by
  unfold first second
  apply hasDerivAt_tsum_of_isPreconnected (ξ.summable.mul_left 25)
    isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (t:=Ioo (-(5/4):ℝ) (5/4)) (y₀:=0) (y:=q)
      (g:=fun (p:ℕ) y=>(p:ℝ)*ξ.coefficient p*y^(p-1))
      (g':=fun (p:ℕ) y=>(p:ℝ)*(p-1:ℕ)*ξ.coefficient p*y^(p-2))
  · intro p y hy
    by_cases hp : ξ.coefficient p=0
    · simp only [hp,mul_zero,zero_mul];exact hasDerivAt_const _ _
    · have he : p-1-1=p-2 := by omega
      convert ((hasDerivAt_id y).pow (p-1)).const_mul ((p:ℝ)*ξ.coefficient p) using 1
      · simp only [Pi.pow_apply,id_eq]
      · simp only [id_eq,he];ring
  · intro p y hy
    have hay : |y|≤5/4 := abs_le.mpr ⟨hy.1.le,hy.2.le⟩
    have hpow : |y|^(p-2)≤(5/4:ℝ)^p := by
      calc
        _≤(5/4:ℝ)^(p-2) := pow_le_pow_left₀ (abs_nonneg _) hay _
        _≤(5/4:ℝ)^p := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
      abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (show (0:ℝ)≤(p-1:ℕ) from Nat.cast_nonneg _),abs_pow]
    have hp' : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast Nat.sub_le p 1
    have hb := degree_sq_power_bound p
    have hn := ξ.nonneg p
    calc
      (p:ℝ)*(p-1:ℕ)*ξ.coefficient p*|y|^(p-2)
          ≤(p:ℝ)^2*ξ.coefficient p*(5/4:ℝ)^p := by
            gcongr
            nlinarith [show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg p]
      _≤25*((2:ℝ)^p*ξ.coefficient p) := by nlinarith
  · norm_num
  · exact ξ.summable_first (by norm_num)
  · exact abs_lt.mp hq

theorem continuousOn_second (ξ : AdmissibleEvenMixture) :
    ContinuousOn ξ.second (Icc (-1:ℝ) 1) := by
  apply continuousOn_tsum (fun p=>by fun_prop) ξ.summable_second_coefficient
  intro p q hq
  have hp : |q|^(p-2)≤1 := pow_le_one₀ (abs_nonneg _) (abs_le.mpr hq)
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (ξ.nonneg p),
    abs_of_nonneg (show (0:ℝ)≤(p:ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (show (0:ℝ)≤(p-1:ℕ) from Nat.cast_nonneg _),abs_pow]
  simpa using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p))

theorem second_pos (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Ioc (0:ℝ) 1) : 0<ξ.second q := by
  rcases ξ.nonzero with ⟨p,hp⟩
  have hdeg := (ξ.active_even p hp.ne').1
  unfold second
  apply Summable.tsum_pos
    (ξ.summable_second (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩))
    (fun n=>mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (ξ.nonneg n)) (pow_nonneg hq.1.le _)) p
  · exact mul_pos (mul_pos (mul_pos (by exact_mod_cast (by omega : 0<p))
      (by exact_mod_cast (by omega : 0<p-1))) hp) (pow_pos hq.1 _)

theorem second_nonneg (ξ : AdmissibleEvenMixture) (q : ℝ) : 0≤ξ.second q := by
  unfold second
  apply tsum_nonneg
  intro p
  by_cases hp : ξ.coefficient p=0
  · simp [hp]
  · have hdeg := ξ.active_even p hp
    have he : Even (p-2) := by
      rcases hdeg.2 with ⟨k,hk⟩
      use k-1
      omega
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (ξ.nonneg p)) (he.pow_nonneg q)

theorem hasDerivAt_value_unit (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Icc (-1:ℝ) 1) : HasDerivAt ξ.value (ξ.first q) q :=
  ξ.hasDerivAt_value (by have:=abs_le.mpr hq;linarith)

theorem hasDerivAt_first_unit (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q∈Icc (-1:ℝ) 1) : HasDerivAt ξ.first (ξ.second q) q :=
  ξ.hasDerivAt_first (by have:=abs_le.mpr hq;linarith)

theorem hasDerivAt_clock (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q|<5/4) :
    HasDerivAt ξ.clock (ξ.second q/ξ.variance) q :=
  (ξ.hasDerivAt_first hq).div_const _

theorem analyticAt_value (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q|<2) : AnalyticAt ℝ ξ.value q := by
  let p := FormalMultilinearSeries.ofScalars ℝ ξ.coefficient
  have hr : (2:ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_summable_norm (r:=(2:ℝ≥0))
    simpa only [p,FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs,
      abs_of_nonneg (ξ.nonneg _),NNReal.coe_ofNat,mul_comm] using ξ.summable
  have hmem : q∈Metric.eball (0:ℝ) p.radius := by
    apply lt_of_lt_of_le _ hr
    simpa [edist_dist,Real.dist_eq,sub_zero] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<2)).mpr hq
  have ha := p.analyticOnNhd q hmem
  change AnalyticAt ℝ (FormalMultilinearSeries.ofScalarsSum ξ.coefficient) q at ha
  change AnalyticAt ℝ (fun x=>∑' n,ξ.coefficient n*x^n) q
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum,smul_eq_mul] using ha

theorem analyticAt_first (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q|<5/4) : AnalyticAt ℝ ξ.first q := by
  have ha := (ξ.analyticAt_value (lt_trans hq (by norm_num))).deriv
  have he : deriv ξ.value =ᶠ[𝓝 q] ξ.first := by
    filter_upwards [(isOpen_Ioo.mem_nhds (abs_lt.mp hq))] with x hx
    exact (ξ.hasDerivAt_value (abs_lt.mpr hx)).deriv
  exact ha.congr he

theorem analyticAt_second (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q|<5/4) : AnalyticAt ℝ ξ.second q := by
  have ha := (ξ.analyticAt_first hq).deriv
  have he : deriv ξ.first =ᶠ[𝓝 q] ξ.second := by
    filter_upwards [(isOpen_Ioo.mem_nhds (abs_lt.mp hq))] with x hx
    exact (ξ.hasDerivAt_first (abs_lt.mpr hx)).deriv
  exact ha.congr he

theorem contDiffOn_value (ξ : AdmissibleEvenMixture) :
    ContDiffOn ℝ ∞ ξ.value (Icc (-1:ℝ) 1) := by
  intro q hq
  exact (ξ.analyticAt_value (by have:=abs_le.mpr hq;linarith)).contDiffAt.contDiffWithinAt

theorem contDiffOn_first (ξ : AdmissibleEvenMixture) :
    ContDiffOn ℝ ∞ ξ.first (Icc (-1:ℝ) 1) := by
  intro q hq
  exact (ξ.analyticAt_first (by have:=abs_le.mpr hq;linarith)).contDiffAt.contDiffWithinAt

theorem contDiffOn_second (ξ : AdmissibleEvenMixture) :
    ContDiffOn ℝ ∞ ξ.second (Icc (-1:ℝ) 1) := by
  intro q hq
  exact (ξ.analyticAt_second (by have:=abs_le.mpr hq;linarith)).contDiffAt.contDiffWithinAt

end FourPapersCommon.AdmissibleEvenMixture
