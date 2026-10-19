-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevScalarChain
public import SlowEquilibration.SphericalSmoothScalarLocalizations

/-! Actual bounded product calculus in the completed spherical Gibbs
Sobolev graph. Smooth scalar square localization and polarization prove
the domain and the literal Leibniz gradient. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator SphericalSmoothScalarLocalizations
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {β : ℝ} {H : Vector N → ℝ}

def productGradientMultiplier (U V : Lp ℝ 2 (gibbsLaw N β H)) (CU CV : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,‖U x‖ ≤ CU) (hV : ∀ᵐ x ∂gibbsLaw N β H,‖V x‖ ≤ CV)
    (G T : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))) :
    PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  WithLp.toLp 2 (fun ij =>
    multiplication (gibbsLaw N β H) V (Lp.aestronglyMeasurable V) CV hV (G ij)+
      multiplication (gibbsLaw N β H) U (Lp.aestronglyMeasurable U) CU hU (T ij))

private theorem scalarGradientMultiplier_ae (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (K : ℝ≥0) (hK : ∀ r,‖deriv Φ r‖ ≤ K) (U : Lp ℝ 2 (gibbsLaw N β H))
    (G : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))) (ij : Fin N × Fin N) :
    scalarGradientMultiplier hN β H hH Φ hΦ K hK U G ij =ᵐ[gibbsLaw N β H]
      fun x => deriv Φ (U x)*(G ij x) :=
  multiplication_ae _ _ _ _ _ _

/-- Bounded products are in the actual completed domain and have the true
Leibniz gradient; no product/chain interface is supplied. -/
theorem sphericalSobolevGraph_bounded_product (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u v : sphericalSobolevGraph hN β H hH) (CU CV : ℝ≥0)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,‖u.val.fst x‖ ≤ CU)
    (hV : ∀ᵐ x ∂gibbsLaw N β H,‖v.val.fst x‖ ≤ CV) :
    ∃ w : sphericalSobolevGraph hN β H hH,
      w.val.fst=multiplication (gibbsLaw N β H) u.val.fst
        (Lp.aestronglyMeasurable u.val.fst) CU hU v.val.fst ∧
      w.val.snd=productGradientMultiplier u.val.fst v.val.fst CU CV hU hV u.val.snd v.val.snd := by
  let U := u.val.fst
  let V := v.val.fst
  let A := (u+v).val.fst
  let B := (u-v).val.fst
  let C : ℝ := CU+CV
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : ∀ᵐ x ∂gibbsLaw N β H,‖A x‖ ≤ C := by
    filter_upwards [hU,hV,Lp.coeFn_add U V] with x hu hv ha
    change A x=U x+V x at ha
    rw [ha]
    exact (norm_add_le _ _).trans (add_le_add hu hv)
  have hB : ∀ᵐ x ∂gibbsLaw N β H,‖B x‖ ≤ C := by
    filter_upwards [hU,hV,Lp.coeFn_sub U V] with x hu hv hb
    change B x=U x-V x at hb
    rw [hb]
    exact (norm_sub_le _ _).trans (add_le_add hu hv)
  obtain ⟨Φ,hΦ,hΦ0,⟨K,hK⟩,hΦeq⟩ := exists_square_localization C hC
  let hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by simp)
  let hL := lipschitzWith_of_nnnorm_deriv_le (hΦ1.differentiable (by norm_num))
    (fun r => show ‖deriv Φ r‖₊ ≤ K from hK r)
  obtain ⟨p,hpValue,hpGradient⟩ := sphericalSobolevGraph_scalar_chain hN β H hH Φ hΦ hΦ0 K hK (u+v)
  obtain ⟨q,hqValue,hqGradient⟩ := sphericalSobolevGraph_scalar_chain hN β H hH Φ hΦ hΦ0 K hK (u-v)
  let w := (1/4 : ℝ) • (p-q)
  have hp : p.val.fst =ᵐ[gibbsLaw N β H] fun x => (A x)^2 := by
    rw [hpValue]
    filter_upwards [hL.coeFn_compLp hΦ0 A,hA] with x hx ha
    have hai : A x∈Icc (-C) C := abs_le.mp (by simpa only [Real.norm_eq_abs] using ha)
    exact hx.trans (hΦeq _ hai).1
  have hq : q.val.fst =ᵐ[gibbsLaw N β H] fun x => (B x)^2 := by
    rw [hqValue]
    filter_upwards [hL.coeFn_compLp hΦ0 B,hB] with x hx hb
    have hbi : B x∈Icc (-C) C := abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
    exact hx.trans (hΦeq _ hbi).1
  refine ⟨w,?_,?_⟩
  · change (1/4 : ℝ) • (p.val.fst-q.val.fst)=multiplication (gibbsLaw N β H) U
      (Lp.aestronglyMeasurable U) CU hU V
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (1/4 : ℝ) (p.val.fst-q.val.fst),
      Lp.coeFn_sub p.val.fst q.val.fst,hp,hq,Lp.coeFn_add U V,Lp.coeFn_sub U V,
      multiplication_ae (gibbsLaw N β H) U (Lp.aestronglyMeasurable U) CU hU V]
        with x hsm hsub hpx hqx hax hbx hmul
    change A x=U x+V x at hax
    change B x=U x-V x at hbx
    rw [hsm,Pi.smul_apply,smul_eq_mul,hsub,Pi.sub_apply,hpx,hqx,hax,hbx,hmul]
    ring
  · apply PiLp.ext
    intro ij
    have hpg : p.val.snd ij =ᵐ[gibbsLaw N β H]
        fun x => deriv Φ (A x)*((u+v).val.snd ij x) := by
      rw [hpGradient]
      exact scalarGradientMultiplier_ae hN β H hH Φ hΦ1 K hK A (u+v).val.snd ij
    have hqg : q.val.snd ij =ᵐ[gibbsLaw N β H]
        fun x => deriv Φ (B x)*((u-v).val.snd ij x) := by
      rw [hqGradient]
      exact scalarGradientMultiplier_ae hN β H hH Φ hΦ1 K hK B (u-v).val.snd ij
    let GU := u.val.snd ij
    let GV := v.val.snd ij
    let MU := multiplication (gibbsLaw N β H) U (Lp.aestronglyMeasurable U) CU hU GV
    let MV := multiplication (gibbsLaw N β H) V (Lp.aestronglyMeasurable V) CV hV GU
    change (1/4 : ℝ) • (p.val.snd ij-q.val.snd ij)=MV+MU
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (1/4 : ℝ) (p.val.snd ij-q.val.snd ij),
      Lp.coeFn_sub (p.val.snd ij) (q.val.snd ij),hpg,hqg,hA,hB,
      Lp.coeFn_add U V,Lp.coeFn_sub U V,Lp.coeFn_add GU GV,Lp.coeFn_sub GU GV,
      multiplication_ae (gibbsLaw N β H) U (Lp.aestronglyMeasurable U) CU hU GV,
      multiplication_ae (gibbsLaw N β H) V (Lp.aestronglyMeasurable V) CV hV GU,
      Lp.coeFn_add MV MU]
        with x hsm hsub hpq hqq ha hb hax hbx hgu hgv hmu hmv hadd
    change A x=U x+V x at hax
    change B x=U x-V x at hbx
    change MU x=U x*GV x at hmu
    change MV x=V x*GU x at hmv
    have hai : A x∈Icc (-C) C := abs_le.mp (by simpa only [Real.norm_eq_abs] using ha)
    have hbi : B x∈Icc (-C) C := abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
    change (GU+GV) x=GU x+GV x at hgu
    change (GU-GV) x=GU x-GV x at hgv
    rw [hsm,Pi.smul_apply,smul_eq_mul,hsub,Pi.sub_apply,hpq,hqq,hadd,Pi.add_apply,hmu,hmv]
    change (1/4 : ℝ)*(deriv Φ (A x)*(GU+GV) x-deriv Φ (B x)*(GU-GV) x)=_
    rw [(hΦeq _ hai).2,(hΦeq _ hbi).2,hax,hbx,hgu,hgv]
    ring

end SlowEquilibration.SphericalForm
