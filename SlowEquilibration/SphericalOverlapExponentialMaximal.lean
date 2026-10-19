-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponentialMarkov
public import StochasticCalculus.ItoMaximal
public import Mathlib.Probability.Martingale.OptionalStopping

/-! Mesh-independent exponential overlap maximal bounds for the original
physical spherical flow. Finite-grid Doob and actual path continuity are used;
no continuous stopping-time theorem or maximal-tail premise is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalC1Dynamics
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section General
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}

theorem nonnegative_submartingale_dyadic_maximal (hM : Submartingale M F P)
    (hnonneg : 0 ≤ M) (a : ℝ≥0) (T : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) * P {omega | (a : ℝ) ^ 2 ≤ dyadicPartitionSqMax M T n omega} ≤
      ENNReal.ofReal (∫ omega,M T omega ∂P) := by
  let u := uniformPartitionTime T (2 ^ n)
  let G := monotoneReindexFiltration F u (monotone_uniformPartitionTime_general T (2 ^ n))
  have hsample : Submartingale (fun k => M (u k)) G P :=
    ⟨fun k => hM.1 (u k),fun k l hkl => hM.2.1 _ _ ((monotone_uniformPartitionTime_general T (2 ^ n)) hkl),
      fun k => hM.2.2 (u k)⟩
  have he : {omega | (a : ℝ) ^ 2 ≤ dyadicPartitionSqMax M T n omega} =
      {omega | (a : ℝ) ≤ (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => M (u k) omega)} := by
    ext omega
    change _ ≤ _ ↔ _ ≤ _
    constructor
    · intro h
      obtain ⟨k,hk,heq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        (fun k => (M (u k) omega) ^ 2)
      change (a : ℝ) ^ 2 ≤ (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (M (u k) omega) ^ 2) at h
      rw [heq] at h
      exact ((sq_le_sq₀ a.coe_nonneg (hnonneg (u k) omega)).mp h).trans (Finset.le_sup' (fun k => M (u k) omega) hk)
    · intro h
      obtain ⟨k,hk,heq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one (fun k => M (u k) omega)
      rw [heq] at h
      change (a : ℝ) ^ 2 ≤ (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (M (u k) omega) ^ 2)
      exact ((sq_le_sq₀ a.coe_nonneg (hnonneg (u k) omega)).mpr h).trans
        (Finset.le_sup' (fun k => (M (u k) omega) ^ 2) hk)
  rw [he]
  have hd := maximal_ineq hsample (fun k omega => hnonneg (u k) omega) (ε := a) (2 ^ n)
  have ht : u (2 ^ n) = T := by
    unfold u uniformPartitionTime
    exact mul_div_cancel_right₀ T (by positivity)
  have hi := setIntegral_le_integral (s := {omega | (a : ℝ) ≤
    (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one (fun k => M (u k) omega)})
    (hM.2.2 (u (2 ^ n))) (.of_forall fun omega => hnonneg _ omega)
  exact hd.trans ((ENNReal.ofReal_le_ofReal hi).trans_eq (by rw [ht]))

theorem continuous_nonnegative_submartingale_maximal (hM : Submartingale M F P)
    (hnonneg : 0 ≤ M) (hcont : ∀ᵐ omega ∂P,Continuous (fun t => M t omega))
    (a : ℝ≥0) (T : ℝ≥0) :
    (a : ℝ≥0∞) * P {omega | ∃ t : ℝ≥0,t ≤ T ∧ (a : ℝ) < M t omega} ≤
      ENNReal.ofReal (∫ omega,M T omega ∂P) := by
  let S : ℕ → Set Ω := fun n => {omega | (a : ℝ) ^ 2 ≤ dyadicPartitionSqMax M T n omega}
  have hS : Monotone S := by
    intro n m hnm omega homega
    exact homega.trans (monotone_dyadicPartitionSqMax M T omega hnm)
  have hcover : {omega | ∃ t : ℝ≥0,t ≤ T ∧ (a : ℝ) < M t omega} ≤ᵐ[P] ⋃ n,S n := by
    filter_upwards [hcont] with omega hc homega
    obtain ⟨t,ht,ha⟩ := homega
    have hsq : (a : ℝ) ^ 2 < (M t omega) ^ 2 := by nlinarith [hnonneg t omega,a.coe_nonneg]
    obtain ⟨n,hn⟩ := exists_lt_dyadicPartitionSqMax_of_continuous M T omega hc ht hsq
    exact mem_iUnion.mpr ⟨n,hn.le⟩
  calc
    _ ≤ (a : ℝ≥0∞) * P (⋃ n,S n) := mul_le_mul_of_nonneg_left (measure_mono_ae hcover) bot_le
    _ = ⨆ n,(a : ℝ≥0∞) * P (S n) := by rw [hS.measure_iUnion,ENNReal.mul_iSup]
    _ ≤ _ := iSup_le (fun n => nonnegative_submartingale_dyadic_maximal hM hnonneg a T n)

end General

variable {N : ℕ}

/-- Genuine one-sided continuous-time overlap excursion tail on a fixed
window for the original C1-gradient physical sphere process. -/
theorem overlap_upper_excursion_tail (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {ell : ℝ} (hell : 0 < ell)
    (δ : ℝ) (T : ℝ≥0) :
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < overlapValue u (process β g hg x t omega) - overlapValue u x} ≤
    Real.exp ((2 * ell * (1 + β * C) + ell ^ 2 / (N : ℝ)) * (T : ℝ) - ell * δ) := by
  let b := |ell| * (1 + β * C)
  let M := overlapSubmartingale β C g hg u x ell
  let a : ℝ≥0 := ⟨Real.exp (ell * (overlapValue u x + δ)),(Real.exp_pos _).le⟩
  have hb : 0 ≤ b := mul_nonneg (abs_nonneg ell) (by positivity)
  have hM := overlapSubmartingale_submartingale hN hβ hC g hg hgrad u x hu hx ell
  have hnonneg := overlapSubmartingale_nonneg β C g hg u x ell
  have hcont : ∀ᵐ omega ∂VectorBrownian.law N,Continuous (fun t => M t omega) := by
    filter_upwards [process_continuous β g hg x] with omega hc
    exact (show Continuous (fun t : ℝ≥0 => Real.exp (b * (t : ℝ))) from by fun_prop).mul
      ((expLinear_contDiff (ell • overlapLinear u)).continuous.comp hc)
  have hmax := continuous_nonnegative_submartingale_maximal hM hnonneg hcont a T
  have hcover : {omega | ∃ t : ℝ≥0,t ≤ T ∧ δ <
      overlapValue u (process β g hg x t omega) - overlapValue u x} ⊆
      {omega | ∃ t : ℝ≥0,t ≤ T ∧ (a : ℝ) < M t omega} := by
    intro omega homega
    obtain ⟨t,ht,hδ⟩ := homega
    refine ⟨t,ht,?_⟩
    have hlt : (a : ℝ) < expOverlap u ell (process β g hg x t omega) := by
      apply Real.exp_lt_exp.mpr
      dsimp [a,expOverlap,expLinear,overlapValue]
      simp only [_root_.smul_apply,smul_eq_mul]
      dsimp [overlapValue] at hδ
      nlinarith
    have hfactor : 1 ≤ Real.exp (b * (t : ℝ)) := Real.one_le_exp_iff.mpr (mul_nonneg hb t.coe_nonneg)
    exact hlt.trans_le (by
      change expOverlap u ell _ ≤ Real.exp (b * (t : ℝ)) * expOverlap u ell _
      nlinarith [Real.exp_pos ((ell • overlapLinear u) (process β g hg x t omega))])
  have hmul := (mul_le_mul_of_nonneg_left (measure_mono hcover) (show (0 : ℝ≥0∞) ≤ a from bot_le)).trans hmax
  have hi := expectation_le_exp_mul hN β g hg x hx (expLinear_contDiff (ell • overlapLinear u))
    (b + ell ^ 2 / (N : ℝ)) (fun y hy => expOverlap_generator_le hN hβ hC g hgrad u hu ell y hy) T
  have hmean : (∫ omega,M T omega ∂VectorBrownian.law N) ≤
      Real.exp ((2 * b + ell ^ 2 / (N : ℝ)) * (T : ℝ) + ell * overlapValue u x) := by
    have hI : (∫ omega,M T omega ∂VectorBrownian.law N) =
        Real.exp (b * (T : ℝ)) * expectation β g hg T (expOverlap u ell) x := integral_const_mul _ _
    rw [hI]
    have hh := mul_le_mul_of_nonneg_left hi (Real.exp_pos (b * (T : ℝ))).le
    apply hh.trans_eq
    unfold expLinear
    simp only [_root_.smul_apply,smul_eq_mul]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp [b,overlapValue]
    ring
  have htot := hmul.trans (ENNReal.ofReal_le_ofReal hmean)
  have hreal := ENNReal.toReal_mono (by finiteness) htot
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  have hdiv : (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < overlapValue u (process β g hg x t omega) - overlapValue u x} ≤
      Real.exp ((2 * b + ell ^ 2 / (N : ℝ)) * (T : ℝ) + ell * overlapValue u x) /
        Real.exp (ell * (overlapValue u x + δ)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hacoe : (a : ℝ) = Real.exp (ell * (overlapValue u x + δ)) := rfl
    rw [hacoe] at hreal
    rw [measureReal_def]
    nlinarith only [hreal]
  apply hdiv.trans_eq
  rw [div_eq_mul_inv,← Real.exp_neg,← Real.exp_add]
  congr 1
  dsimp [b]
  rw [abs_of_pos hell]
  ring

theorem overlap_upper_short_window_tail (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < overlapValue u (process β g hg x t omega) - overlapValue u x} ≤
    Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hTr : (0 : ℝ) < T := hT
  let ell := (N : ℝ) * δ / (4 * (T : ℝ))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have ht := overlap_upper_excursion_tail hN hβ hC g hg hgrad u x hu hx hell δ T
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  have he1 : ell ^ 2 / (N : ℝ) * (T : ℝ) = ell * δ / 4 := by
    dsimp [ell]
    field_simp
  have he2 : ell * δ / 4 = (N : ℝ) * δ ^ 2 / (16 * (T : ℝ)) := by
    dsimp [ell]
    field_simp
    norm_num
  have hb := mul_le_mul_of_nonneg_left hshort (half_pos hell).le
  rw [add_mul,he1]
  simp only [neg_mul,neg_div]
  rw [← he2]
  nlinarith

lemma overlapValue_neg_left (u x : State N) : overlapValue (-u) x = -overlapValue u x := by
  rw [overlapValue_eq,overlapValue_eq,inner_neg_left,neg_div]

/-- Full two-sided exponential maximal tail on a fixed window, derived
for the actual C1-gradient physical sphere process from its primitive
uniform gradient norm bound. -/
theorem overlap_absolute_short_window_tail (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < |overlapValue u (process β g hg x t omega) - overlapValue u x|} ≤
    2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  have hnu : OnSphere (-u) := by
    unfold OnSphere at hu ⊢
    simpa only [inner_neg_left,inner_neg_right,neg_neg] using hu
  let A : Set (VectorBrownian.Space N) := {omega | ∃ t : ℝ≥0,t ≤ T ∧
    δ < overlapValue u (process β g hg x t omega) - overlapValue u x}
  let B : Set (VectorBrownian.Space N) := {omega | ∃ t : ℝ≥0,t ≤ T ∧
    δ < overlapValue (-u) (process β g hg x t omega) - overlapValue (-u) x}
  have hsub : {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < |overlapValue u (process β g hg x t omega) - overlapValue u x|} ⊆ A ∪ B := by
    intro omega homega
    obtain ⟨t,ht,hd⟩ := homega
    by_cases hr : 0 ≤ overlapValue u (process β g hg x t omega) - overlapValue u x
    · rw [abs_of_nonneg hr] at hd
      exact Or.inl ⟨t,ht,hd⟩
    · rw [abs_of_neg (lt_of_not_ge hr)] at hd
      apply Or.inr
      refine ⟨t,ht,?_⟩
      rw [overlapValue_neg_left,overlapValue_neg_left]
      linarith
  have ha := overlap_upper_short_window_tail hN hβ hC g hg hgrad u x hu hx hδ T hT hshort
  have hb := overlap_upper_short_window_tail hN hβ hC g hg hgrad (-u) x hnu hx hδ T hT hshort
  have hmeasure := (measureReal_mono (μ := VectorBrownian.law N) hsub).trans
    (measureReal_union_le (μ := VectorBrownian.law N) A B)
  dsimp [A,B] at hmeasure
  linarith

end SlowEquilibration.SphericalOverlapExponential
