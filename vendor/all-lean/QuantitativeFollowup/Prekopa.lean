module
public import QuantitativeFollowup.External.PrekopaLeindler
public import Mathlib.Tactic

@[expose] public section

/-! The standard convex-combination form of the genuine finite-dimensional
Prékopa--Leindler theorem. The imported proof is retained with provenance;
this wrapper supplies the change of variables and cancels its Jacobians. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup

theorem lintegral_inv_smul_pi {n : ℕ} (a : ℝ) (ha : 0 < a)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (a⁻¹ • x)) = ENNReal.ofReal (a ^ n) * ∫⁻ x, f x := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := a⁻¹ • LinearMap.id
  have hdet : LinearMap.det L = a⁻¹ ^ n := by
    simp [L, LinearMap.det_smul]
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := L) (by rw [hdet]; exact pow_ne_zero _ (inv_ne_zero ha.ne'))
  have hL : Measurable (fun x : Fin n → ℝ => L x) := L.continuous_of_finiteDimensional.measurable
  change (∫⁻ x, f (L x)) = _
  rw [←lintegral_map hf hL, hmap, lintegral_smul_measure, hdet]
  simp only [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg ha.le _), smul_eq_mul]

theorem prekopa_leindler {d : ℕ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (f g h : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1-θ) * g y ^ θ ≤ h ((1-θ) • x + θ • y)) :
    (∫⁻ x, f x) ^ (1-θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by
  have ha : 0 < 1-θ := sub_pos.mpr hθ.2
  let a := ENNReal.ofReal ((1-θ)^((d+1)*(1-θ)))
  let b := ENNReal.ofReal (θ^((d+1)*θ))
  have hab0 : a*b ≠ 0 := mul_ne_zero
    ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ha _)).ne')
    ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hθ.1 _)).ne')
  have habt : a*b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ)) = a*b := by
    exact ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)
  have hp := PrekopaFoundation.prekopa_leindler (d := d) (θ := θ)
    (f := fun x => f ((1-θ)⁻¹ • x))
    (g := fun x => g (θ⁻¹ • x)) (h := h)
    ⟨hθ.1,hθ.2,hf.comp (by fun_prop),hg.comp (by fun_prop),hh,?_⟩
  · rw [lintegral_inv_smul_pi _ ha _ hf,
      lintegral_inv_smul_pi _ hθ.1 _ hg] at hp
    try simp only [Nat.cast_add,Nat.cast_one] at hp
    rw [ENNReal.ofReal_inv_of_pos (mul_pos (Real.rpow_pos_of_pos ha _)
      (Real.rpow_pos_of_pos hθ.1 _)),hc] at hp
    have hpa : ENNReal.ofReal ((1-θ)^(d+1)) ^ (1-θ) = a := by
      rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ha.le _) ha.le]
      rw [←Real.rpow_natCast, ←Real.rpow_mul ha.le]
      simp only [a,Nat.cast_add,Nat.cast_one]
    have hpb : ENNReal.ofReal (θ^(d+1)) ^ θ = b := by
      rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hθ.1.le _) hθ.1.le]
      rw [←Real.rpow_natCast, ←Real.rpow_mul hθ.1.le]
      simp only [b,Nat.cast_add,Nat.cast_one]
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le,
      ENNReal.mul_rpow_of_nonneg _ _ hθ.1.le,hpa,hpb] at hp
    convert hp using 1
    calc
      _ = ((a*b)⁻¹*(a*b))*((∫⁻ x, f x)^(1-θ)*(∫⁻ x, g x)^θ) := by
        rw [ENNReal.inv_mul_cancel hab0 habt,one_mul]
      _ = _ := by ac_rfl
  · intro x y
    simpa only [smul_smul,mul_inv_cancel₀ ha.ne',mul_inv_cancel₀ hθ.1.ne',one_smul]
      using hfg ((1-θ)⁻¹ • x) (θ⁻¹ • y)

end QuantitativeFollowup
