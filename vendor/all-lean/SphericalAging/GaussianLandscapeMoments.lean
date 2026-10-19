module

public import SphericalAging.GaussianLandscape
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

public section

/-!
# Uniform Gaussian landscape moments

The proved actual Gaussian tail is integrated by layer cake. A single
exponential square moment bound dominates every nonnegative real power and
every exponential moment, uniformly over dimensions N≥1.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SphericalAging.GaussianLandscapeMoments
open FiniteModel GaussianLandscape

@[expose] def expSquareDerivative (x : ℝ) : ℝ := x/16*Real.exp (x^2/32)

@[expose] def tailEnvelope (p : ℕ) (x : ℝ) : ℝ :=
  (Ioc 0 (landscapeThreshold p)).indicator expSquareDerivative x+
    |x|/8*Real.exp (-x^2/32)

theorem expSquareDerivative_continuous : Continuous expSquareDerivative := by
  unfold expSquareDerivative
  fun_prop

theorem expSquareDerivative_nonnegative {x : ℝ} (hx : 0 ≤ x) : 0 ≤ expSquareDerivative x :=
  mul_nonneg (div_nonneg hx (by norm_num)) (Real.exp_nonneg _)

theorem expSquare_integral {q : ℝ} (_hq : 0 ≤ q) :
    (∫ x in (0 : ℝ)..q, expSquareDerivative x)=Real.exp (q^2/32)-1 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (y^2/32)) (expSquareDerivative x) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 32).exp using 1
    · funext y
      rfl
    · unfold expSquareDerivative
      simp only [id_eq,mul_one,Pi.pow_apply]
      ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (expSquareDerivative_continuous.intervalIntegrable 0 q)
  simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_div,Real.exp_zero] using hh

theorem tailEnvelope_nonnegative (p : ℕ) (x : ℝ) : 0 ≤ tailEnvelope p x := by
  unfold tailEnvelope
  apply add_nonneg
  · by_cases hx : x ∈ Ioc 0 (landscapeThreshold p)
    · rw [indicator_of_mem hx]
      exact expSquareDerivative_nonnegative hx.1.le
    · rw [indicator_of_notMem hx]
  · positivity

theorem tailEnvelope_integrable (p : ℕ) : Integrable (tailEnvelope p) volume := by
  have hfirst : Integrable ((Ioc 0 (landscapeThreshold p)).indicator expSquareDerivative) volume := by
    exact ((expSquareDerivative_continuous.integrableOn_Icc (μ := volume) (a := 0) (b := landscapeThreshold p)).mono_set Ioc_subset_Icc_self).integrable_indicator
      measurableSet_Ioc
  have hsecond : Integrable (fun x : ℝ => |x|/8*Real.exp (-x^2/32)) volume := by
    have hi := (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)/32) (by norm_num)).norm.const_mul (1/8 : ℝ)
    apply hi.congr (ae_of_all _ (fun x => ?_))
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have heq : -(1/32 : ℝ)*x^2= -x^2/32 := by ring
    rw [heq]
    ring
  exact hfirst.add hsecond

@[expose] def expSquareCeiling (p : ℕ) : ℝ≥0∞ :=
  1+∫⁻ x : ℝ, ENNReal.ofReal (tailEnvelope p x)

theorem expSquareCeiling_ne_top (p : ℕ) : expSquareCeiling p ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.one_ne_top
  · exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (tailEnvelope_nonnegative p))).mp
      (tailEnvelope_integrable p).hasFiniteIntegral |>.ne

theorem actual_tail_derivative_bound {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p) {x : ℝ}
    (hx : 0 < x) :
    (disorderLaw N p) {J | x < landscapeNorm N p J}*ENNReal.ofReal (expSquareDerivative x) ≤
      ENNReal.ofReal (tailEnvelope p x) := by
  have hq : (disorderLaw N p) {J | x < landscapeNorm N p J}=
      ENNReal.ofReal ((disorderLaw N p).real {J | x < landscapeNorm N p J}) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hq,← ENNReal.ofReal_mul (measureReal_nonneg : 0 ≤ (disorderLaw N p).real {J | x < landscapeNorm N p J})]
  apply ENNReal.ofReal_le_ofReal
  by_cases hsmall : x ≤ landscapeThreshold p
  · have hprob : (disorderLaw N p).real {J | x < landscapeNorm N p J} ≤ 1 :=
      measureReal_le_one
    unfold tailEnvelope
    rw [indicator_of_mem (show x ∈ Ioc 0 (landscapeThreshold p) from ⟨hx,hsmall⟩)]
    have hh := mul_le_mul_of_nonneg_right hprob (expSquareDerivative_nonnegative hx.le)
    have hn : 0 ≤ |x|/8*Real.exp (-x^2/32) := by positivity
    linarith
  · have htail0 := landscape_tail_dimension (by omega : 0 < N) hp (le_of_not_ge hsmall)
    have htail : (disorderLaw N p).real {J | x < landscapeNorm N p J} ≤
        2*Real.exp (-x^2/16) := by
      apply htail0.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg x]
    have hh := mul_le_mul_of_nonneg_right htail (expSquareDerivative_nonnegative hx.le)
    unfold tailEnvelope
    rw [indicator_of_notMem (show x ∉ Ioc 0 (landscapeThreshold p) from fun hh => hsmall hh.2),zero_add]
    have heq : (2*Real.exp (-x^2/16))*expSquareDerivative x=|x|/8*Real.exp (-x^2/32) := by
      unfold expSquareDerivative
      rw [abs_of_pos hx]
      calc
        _ = x/8*(Real.exp (-x^2/16)*Real.exp (x^2/32)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    exact heq ▸ hh

/-- A finite p-only upper bound for the actual exponential square moment. -/
theorem uniform_expSquare_lintegral {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p) :
    (∫⁻ J : Disorder N p, ENNReal.ofReal (Real.exp ((landscapeNorm N p J)^2/32)) ∂disorderLaw N p) ≤
      expSquareCeiling p := by
  let q : Disorder N p → ℝ := landscapeNorm N p
  have hq : ∀ J, 0 ≤ q J := landscapeNorm_nonnegative N p
  have hqm : AEMeasurable q (disorderLaw N p) := (landscapeNorm_continuous N p).measurable.aemeasurable
  have hprim (J : Disorder N p) := expSquare_integral (hq J)
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul (disorderLaw N p) (ae_of_all _ hq) hqm
    (fun t _ => expSquareDerivative_continuous.intervalIntegrable 0 t)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => expSquareDerivative_nonnegative hx.le))
  have hb : (∫⁻ x in Ioi (0 : ℝ),
      (disorderLaw N p) {J | x < q J}*ENNReal.ofReal (expSquareDerivative x)) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal (tailEnvelope p x) := by
    calc
      _ ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (tailEnvelope p x) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact actual_tail_derivative_bound hN hp hx
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have he : ∀ J, ENNReal.ofReal (Real.exp ((q J)^2/32))=
      1+ENNReal.ofReal (∫ x in (0 : ℝ)..q J, expSquareDerivative x) := by
    intro J
    rw [hprim J]
    have hh : 0 ≤ Real.exp ((q J)^2/32)-1 := by
      exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) hh]
    congr 1
    ring
  change (∫⁻ J : Disorder N p, ENNReal.ofReal (Real.exp ((q J)^2/32)) ∂disorderLaw N p) ≤ expSquareCeiling p
  simp_rw [he]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const,measure_univ,one_mul]
  rw [hcake]
  exact add_le_add (le_refl 1) hb

/-- The tensor operator norm is exactly the manuscript's supremum on unit vectors. -/
theorem tensor_unit_sphere_isLUB {N p : ℕ} (hN : 1 ≤ N) (f : TensorForm N p) :
    IsLUB (Set.range (fun v : {v : Fin p → Vector N // ∀ k, ‖v k‖=1} => |f v.val|)) ‖f‖ := by
  let i : Fin N := ⟨0,by omega⟩
  let u : Vector N := PiLp.single 2 i (1 : ℝ)
  have hu : ‖u‖=1 := by simp [u]
  let v0 : {v : Fin p → Vector N // ∀ k, ‖v k‖=1} := ⟨fun _ => u,fun _ => hu⟩
  constructor
  · intro a ha
    obtain ⟨v,rfl⟩ := ha
    have hh := f.le_opNorm v.val
    simpa only [v.property,Finset.prod_const_one,mul_one,Real.norm_eq_abs] using hh
  · intro B hB
    have hBn : 0 ≤ B := (abs_nonneg (f v0.val)).trans (hB ⟨v0,rfl⟩)
    apply multilinear_norm_le_of_unit_bound f hBn
    intro v hv
    simpa only [Real.norm_eq_abs] using hB ⟨⟨v,hv⟩,rfl⟩

/-- Exact identification with Q_N as defined by the manuscript's unit-sphere supremum. -/
theorem landscapeNorm_isLUB {N p : ℕ} (hN : 1 ≤ N) (J : Disorder N p) :
    IsLUB (Set.range (fun v : {v : Fin p → Vector N // ∀ k, ‖v k‖=1} =>
      |tensorForm N p J v.val|/Real.sqrt N)) (landscapeNorm N p J) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  constructor
  · intro a ha
    obtain ⟨v,rfl⟩ := ha
    exact div_le_div_of_nonneg_right ((tensor_unit_sphere_isLUB hN (tensorForm N p J)).1 ⟨v,rfl⟩) hs.le
  · intro B hB
    unfold landscapeNorm
    apply (div_le_iff₀ hs).mpr
    apply (tensor_unit_sphere_isLUB hN (tensorForm N p J)).2
    intro a ha
    obtain ⟨v,rfl⟩ := ha
    exact (div_le_iff₀ hs).mp (hB ⟨v,rfl⟩)

/-- The p-only finite constant used for real powers and exponential moments. -/
@[expose] def momentCeiling (p : ℕ) (b : ℝ) : ℝ :=
  Real.exp (8*b^2)*(expSquareCeiling p).toReal

theorem expSquare_integrable {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p) :
    Integrable (fun J : Disorder N p => Real.exp ((landscapeNorm N p J)^2/32))
      (disorderLaw N p) := by
  constructor
  · exact (Real.continuous_exp.comp ((landscapeNorm_continuous N p).pow 2 |>.div_const 32)).aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun J => Real.exp_nonneg _))).mpr
    exact lt_of_le_of_lt (uniform_expSquare_lintegral hN hp) (lt_top_iff_ne_top.mpr (expSquareCeiling_ne_top p))

theorem expSquare_expectation_bound {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p) :
    (∫ J : Disorder N p, Real.exp ((landscapeNorm N p J)^2/32) ∂disorderLaw N p) ≤
      (expSquareCeiling p).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun J => Real.exp_nonneg _))
    (expSquare_integrable hN hp).aestronglyMeasurable]
  exact ENNReal.toReal_mono (expSquareCeiling_ne_top p) (uniform_expSquare_lintegral hN hp)

theorem exp_linear_le_exp_square (b q : ℝ) :
    Real.exp (b*q) ≤ Real.exp (8*b^2)*Real.exp (q^2/32) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (q-16*b)]

theorem rpow_le_exp_square {k q : ℝ} (hk : 0 ≤ k) (hq : 0 ≤ q) :
    q^k ≤ Real.exp (8*k^2)*Real.exp (q^2/32) := by
  by_cases hq0 : q=0
  · subst q
    exact (Real.zero_rpow_le_one k).trans (by simp only [zero_pow (by norm_num : 2 ≠ 0),zero_div,Real.exp_zero,mul_one]; exact Real.one_le_exp (by positivity))
  · rw [Real.rpow_def_of_pos (lt_of_le_of_ne hq (Ne.symm hq0))]
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Real.log_le_self hq) hk)).trans
    simpa [mul_comm] using exp_linear_le_exp_square k q

/-- Genuine expectation control under the actual Gaussian tensor law from pointwise domination. -/
theorem expectation_bound_of_exp_square_domination {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p)
    {f : Disorder N p → ℝ} (hf : AEStronglyMeasurable f (disorderLaw N p))
    (hn : ∀ J, 0 ≤ f J) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ J, f J ≤ c*Real.exp ((landscapeNorm N p J)^2/32)) :
    Integrable f (disorderLaw N p) ∧
      (∫ J, f J ∂disorderLaw N p) ≤ c*(expSquareCeiling p).toReal := by
  have hi := (expSquare_integrable hN hp).const_mul c
  have hfi : Integrable f (disorderLaw N p) :=
    hi.mono_nonneg hf (ae_of_all _ hn) (ae_of_all _ hb)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ J : Disorder N p, c*Real.exp ((landscapeNorm N p J)^2/32) ∂disorderLaw N p :=
      integral_mono hfi hi hb
    _ = c*(∫ J : Disorder N p, Real.exp ((landscapeNorm N p J)^2/32) ∂disorderLaw N p) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (expSquare_expectation_bound hN hp) hc

/-- All finite real exponential moments are uniformly bounded in the actual dimension N. -/
theorem uniform_exponential_moment {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p) (b : ℝ) :
    Integrable (fun J : Disorder N p => Real.exp (b*landscapeNorm N p J)) (disorderLaw N p) ∧
      (∫ J : Disorder N p, Real.exp (b*landscapeNorm N p J) ∂disorderLaw N p) ≤ momentCeiling p b := by
  apply expectation_bound_of_exp_square_domination hN hp
  · exact (Real.continuous_exp.comp ((landscapeNorm_continuous N p).const_mul b)).aestronglyMeasurable
  · intro J; exact Real.exp_nonneg _
  · exact Real.exp_nonneg _
  · intro J; exact exp_linear_le_exp_square b _

/-- Every nonnegative finite real power has a uniform actual Gaussian expectation bound. -/
theorem uniform_real_power_moment {N p : ℕ} (hN : 1 ≤ N) (hp : 0 < p)
    {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun J : Disorder N p => (landscapeNorm N p J)^k) (disorderLaw N p) ∧
      (∫ J : Disorder N p, (landscapeNorm N p J)^k ∂disorderLaw N p) ≤ momentCeiling p k := by
  apply expectation_bound_of_exp_square_domination hN hp
  · exact ((Real.continuous_rpow_const hk).comp (landscapeNorm_continuous N p)).aestronglyMeasurable
  · intro J; exact Real.rpow_nonneg (landscapeNorm_nonnegative N p J) _
  · exact Real.exp_nonneg _
  · intro J; exact rpow_le_exp_square hk (landscapeNorm_nonnegative N p J)

/-- The complete probabilistic assertions of Lemma 3.6, for the actual ordered tensor. -/
theorem landscape_probabilistic_bounds (p : ℕ) (hp : 0 < p) :
    (∀ k : ℝ, 0 ≤ k → ∃ M : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun J : Disorder N p => (landscapeNorm N p J)^k) (disorderLaw N p) ∧
        (∫ J : Disorder N p, (landscapeNorm N p J)^k ∂disorderLaw N p) ≤ M) ∧
    (∀ b : ℝ, ∃ M : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun J : Disorder N p => Real.exp (b*landscapeNorm N p J)) (disorderLaw N p) ∧
        (∫ J : Disorder N p, Real.exp (b*landscapeNorm N p J) ∂disorderLaw N p) ≤ M) ∧
    (∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      (disorderLaw N p).real {J | A < landscapeNorm N p J} ≤ Real.exp (-c*N)) := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    exact ⟨momentCeiling p k,fun N hN => uniform_real_power_moment hN hp hk⟩
  · intro b
    exact ⟨momentCeiling p b,fun N hN => uniform_exponential_moment hN hp b⟩
  · refine ⟨landscapeThreshold p+4,1,by linarith [landscapeThreshold_pos p],by norm_num,?_⟩
    intro N hN
    simpa only [neg_one_mul] using landscape_exponential_dimension_bound hN hp

end SphericalAging.GaussianLandscapeMoments
