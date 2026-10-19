module
public import QuantitativeFollowup.Prekopa
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Genuine log-concavity of finite-dimensional marginals, obtained from
Prékopa--Leindler with all integrals interpreted as Lebesgue integrals. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativeFollowup

theorem integral_exp_neg_weighted {d : ℕ} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (V₀ V₁ Vθ : (Fin (d+1) → ℝ) → ℝ)
    (hV₀ : Measurable V₀) (hV₁ : Measurable V₁) (hVθ : Measurable Vθ)
    (hI₀ : Integrable (fun x => Real.exp (-V₀ x)))
    (hI₁ : Integrable (fun x => Real.exp (-V₁ x)))
    (hIθ : Integrable (fun x => Real.exp (-Vθ x)))
    (hconv : ∀ x y, Vθ ((1-θ) • x + θ • y) ≤ (1-θ)*V₀ x+θ*V₁ y) :
    (∫ x, Real.exp (-V₀ x))^(1-θ) * (∫ x, Real.exp (-V₁ x))^θ ≤
      ∫ x, Real.exp (-Vθ x) := by
  have hp := prekopa_leindler hθ
    (fun x => ENNReal.ofReal (Real.exp (-V₀ x)))
    (fun x => ENNReal.ofReal (Real.exp (-V₁ x)))
    (fun x => ENNReal.ofReal (Real.exp (-Vθ x)))
    (by fun_prop) (by fun_prop) (by fun_prop) (fun x y => ?_)
  · rw [←ofReal_integral_eq_lintegral_ofReal hI₀ (.of_forall fun x => (Real.exp_pos _).le),
      ←ofReal_integral_eq_lintegral_ofReal hI₁ (.of_forall fun x => (Real.exp_pos _).le),
      ←ofReal_integral_eq_lintegral_ofReal hIθ (.of_forall fun x => (Real.exp_pos _).le),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (Real.exp_pos _).le)
        (sub_pos.mpr hθ.2).le,
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (Real.exp_pos _).le) hθ.1.le,
      ←ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg fun x => (Real.exp_pos _).le) _)] at hp
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => (Real.exp_pos _).le)).mp hp
  · rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (sub_pos.mpr hθ.2).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hθ.1.le,
      ←ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp,Real.log_exp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := hconv x y
    nlinarith

theorem log_integral_exp_neg_weighted {d : ℕ} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (V₀ V₁ Vθ : (Fin (d+1) → ℝ) → ℝ)
    (hV₀ : Measurable V₀) (hV₁ : Measurable V₁) (hVθ : Measurable Vθ)
    (hI₀ : Integrable (fun x => Real.exp (-V₀ x)))
    (hI₁ : Integrable (fun x => Real.exp (-V₁ x)))
    (hIθ : Integrable (fun x => Real.exp (-Vθ x)))
    (hconv : ∀ x y, Vθ ((1-θ) • x + θ • y) ≤ (1-θ)*V₀ x+θ*V₁ y) :
    (1-θ)*Real.log (∫ x, Real.exp (-V₀ x)) +
      θ*Real.log (∫ x, Real.exp (-V₁ x)) ≤ Real.log (∫ x, Real.exp (-Vθ x)) := by
  have hpos₀ : 0 < ∫ x, Real.exp (-V₀ x) := integral_exp_pos hI₀
  have hpos₁ : 0 < ∫ x, Real.exp (-V₁ x) := integral_exp_pos hI₁
  have hp := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hpos₀ _) (Real.rpow_pos_of_pos hpos₁ _))
    (integral_exp_neg_weighted hθ V₀ V₁ Vθ hV₀ hV₁ hVθ hI₀ hI₁ hIθ hconv)
  rwa [Real.log_mul (Real.rpow_pos_of_pos hpos₀ _).ne'
    (Real.rpow_pos_of_pos hpos₁ _).ne',Real.log_rpow hpos₀,Real.log_rpow hpos₁] at hp

theorem concaveOn_log_integral_exp_neg {d : ℕ} (S : Set ℝ) (hS : Convex ℝ S)
    (W : ℝ → (Fin (d+1) → ℝ) → ℝ)
    (hW : ConvexOn ℝ (S ×ˢ (univ : Set (Fin (d+1) → ℝ))) (Function.uncurry W))
    (hM : ∀ t ∈ S, Measurable (W t))
    (hI : ∀ t ∈ S, Integrable (fun x => Real.exp (-W t x))) :
    ConcaveOn ℝ S (fun t => Real.log (∫ x, Real.exp (-W t x))) := by
  refine ⟨hS,?_⟩
  intro t ht u hu a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0,hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0,ha1]
  have ha' : 0 < a := lt_of_le_of_ne ha (by intro he; exact ha0 he.symm)
  have hb' : 0 < b := lt_of_le_of_ne hb (by intro he; exact hb0 he.symm)
  have hb1 : b < 1 := by linarith
  have hab' : 1-b = a := by linarith
  have hv : a*t+b*u ∈ S := by simpa only [smul_eq_mul] using hS ht hu ha hb hab
  have hp := log_integral_exp_neg_weighted ⟨hb',hb1⟩ (W t) (W u) (W (a*t+b*u))
    (hM t ht) (hM u hu) (hM _ hv) (hI t ht) (hI u hu) (hI _ hv) (fun x y => ?_)
  · simpa only [hab',smul_eq_mul] using hp
  · have hh := hW.2 (show (t,x) ∈ S ×ˢ univ from ⟨ht,mem_univ _⟩)
      (show (u,y) ∈ S ×ˢ univ from ⟨hu,mem_univ _⟩) ha hb hab
    simpa only [hab',Function.uncurry,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using hh

end QuantitativeFollowup
