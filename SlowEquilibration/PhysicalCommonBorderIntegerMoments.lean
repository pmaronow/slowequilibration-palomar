-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalCommonBorderMoments
public import SlowEquilibration.BorderFactorIntegerMoments

/-! Genuine every integer-order moment of the literal full physical bordered determinant,
with all ordinary integrability proved on its original common space. -/
@[expose] public section
namespace SlowEquilibration.PhysicalCommonBorderMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open GOEAsymptotics GOEScaling GOEPhysicalPotential GOEPhysicalClippedDeterminantMoments
open OneBorderMoments BorderFactorIntegerMoments
open scoped Topology BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- A true physical GOE bulk and primitive ordinary border moments imply
the full determinant integer moment, even if all border randomness depends
on the bulk. The clipped moment input is derived by the uniform GOE theorem. -/
theorem full_border_integer_moment_eventually (r : ℕ) (hr : 1 ≤ r) {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g / (2 * Real.sqrt b)) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n + 1 ≤ N → ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), Measurable W →
        HasLaw W (SphericalGaussianJet.goeLaw (n + 1) N b) P →
      (∀ x, (W x).IsHermitian) →
      ∀ (a : Ω → ℝ) (u : Ω → EuclideanSpace ℝ (Fin (n + 1))), Measurable a → Measurable u →
      ∀ L Ca Cu : ℝ, (scaleFactor n N b * ρ)⁻¹ ≤ L →
      Integrable (fun x => |a x| ^ (2*r)) P → Integrable (fun x => ‖u x‖ ^ (4*r)) P →
      (∫ x, |a x| ^ (2*r) ∂P) ≤ Ca → (∫ x, ‖u x‖ ^ (4*r) ∂P) ≤ Cu →
      0 < physicalMean n N b k ∧
      Integrable (fun x => (fullBorder W k a u x / physicalMean n N b k) ^ r) P ∧
      (∫ x, (fullBorder W k a u x / physicalMean n N b k) ^ r ∂P) ≤
        Real.sqrt ((2 : ℝ) ^ (2*r) * Real.exp (4*b*(2*r)^2/g^2)) *
          Real.sqrt ((2:ℝ)^(4*r)*(|k|^(2*r)+Ca)+(2:ℝ)^(2*r)*L^(2*r)*Cu) := by
  filter_upwards [physical_clipped_normalized_moments_eventually hb hg hρ hρg,
    GOESharpMoments.goe_determinant_moments_eventually hb hg] with n hclip hraw
  intro N hN k hk Ω _ P _ W hW hLaw hSym a u ha hu L Ca Cu hL haI huI haM huM
  let m := physicalMean n N b k
  let κ := scaleFactor n N b * ρ
  have hNp : 0 < N := by omega
  have hκ : 0 < κ := mul_pos (scaleFactor_pos n hNp hb) hρ
  have hm : 0 < m := (hraw N hN k hk).2.1
  have hcast : 2*(r:ℝ)=((2*r:ℕ):ℝ) := by norm_cast
  have hBF := factor_integer_moment k (2*r) hκ hL a u ha hu haI
    (by simpa only [show 2*(2*r)=4*r by omega] using huI) haM
    (by simpa only [show 2*(2*r)=4*r by omega] using huM)
  have hClip := hclip N hN k hk ((2*r : ℕ) : ℝ) (by positivity)
  have hEI := hLaw.integrable_fun_comp hClip.1
  have hEM := hLaw.integral_comp
    (((matrixClippedDet_measurable n k κ).div_const m).pow_const ((2*r : ℕ) : ℝ)).aestronglyMeasurable
  have hdom : ∀ᵐ x ∂P, fullBorder W k a u x / m ≤
      (matrixClippedDet n k κ (W x) / m) * factor k κ a u x := by
    filter_upwards [] with x
    have hp := fullBorder_clipped_bound (W x) (hSym x) k (a x) (u x) hκ
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by unfold factor; ring)
  have h := moment_of_product_domination
    (fun x => fullBorder W k a u x / m) (fun x => matrixClippedDet n k κ (W x) / m)
    (factor k κ a u) ((fullBorder_measurable hW k ha hu).div_const m)
    (((matrixClippedDet_measurable n k κ).comp hW).div_const m)
    (factor_measurable k κ ha hu) (fun x => div_nonneg (abs_nonneg _) hm.le)
    (fun x => div_nonneg (matrixClippedDet_pos n k κ (W x)).le hm.le)
    (factor_nonneg k hκ a u) hdom (r := (r : ℝ)) (by positivity)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat, m, κ] using hEI)
    (by simpa only [hcast, Real.rpow_natCast] using hBF.1)
  refine ⟨hm, by simpa only [Real.rpow_natCast,m] using h.1, ?_⟩
  have hBound : (∫ x, (matrixClippedDet n k κ (W x) / m) ^ (2 * (r : ℝ)) ∂P) ≤
      (2 : ℝ) ^ (2*r) * Real.exp (4*b*(2*r)^2/g^2) := by
    have hEM' : (∫ x, (matrixClippedDet n k κ (W x) / m) ^ (2 * (r : ℝ)) ∂P) =
      ∫ x, (matrixClippedDet n k κ x / m) ^ (2 * (r : ℝ))
        ∂SphericalGaussianJet.goeLaw (n+1) N b := by
      simpa only [Function.comp_def,Nat.cast_mul,Nat.cast_ofNat] using hEM
    rw [hEM']
    simpa only [hcast,Real.rpow_natCast,m,κ] using hClip.2
  have hFBound : (∫ x, factor k κ a u x ^ (2 * (r : ℝ)) ∂P) ≤
      (2:ℝ)^(4*r)*(|k|^(2*r)+Ca)+(2:ℝ)^(2*r)*L^(2*r)*Cu := by
    simpa only [hcast, Real.rpow_natCast, show 2*(2*r)=4*r by omega] using hBF.2
  have hh := h.2.trans (mul_le_mul (Real.sqrt_le_sqrt hBound) (Real.sqrt_le_sqrt hFBound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simpa only [Real.rpow_natCast,m] using hh

end
end SlowEquilibration.PhysicalCommonBorderMoments
