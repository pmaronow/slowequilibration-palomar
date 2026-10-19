-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticTrace

/-! Genuine ordinary quadratic L² stability under a deterministic vector
translation, with all integrability obligations included. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma quadratic_translation_abs_le (S : E →L[ℝ] E) (u v : E) {M : ℝ}
    (hM : 0 ≤ M) (hv : ‖v‖ ≤ M) :
    |inner ℝ (u+v) (S (u+v))-inner ℝ u (S u)| ≤ ‖S‖*M*(2*‖u‖+M) := by
  have heq : inner ℝ (u+v) (S (u+v))-inner ℝ u (S u)=
      inner ℝ u (S v)+inner ℝ v (S u)+inner ℝ v (S v) := by
    rw [map_add,inner_add_left,inner_add_right,inner_add_right]
    ring
  rw [heq]
  have h1 : |inner ℝ u (S v)| ≤ ‖S‖*M*‖u‖ := by
    calc
      _ ≤ ‖u‖*‖S v‖:=abs_real_inner_le_norm _ _
      _ ≤ ‖u‖*(‖S‖*M):=mul_le_mul_of_nonneg_left
        ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) (norm_nonneg _)
      _=_:=by ring
  have h2 : |inner ℝ v (S u)| ≤ ‖S‖*M*‖u‖ := by
    calc
      _ ≤ ‖v‖*‖S u‖:=abs_real_inner_le_norm _ _
      _ ≤ M*(‖S‖*‖u‖):=mul_le_mul hv (S.le_opNorm _) (norm_nonneg _) hM
      _=_:=by ring
  have h3 : |inner ℝ v (S v)| ≤ ‖S‖*M^2 := by
    calc
      _ ≤ ‖v‖*‖S v‖:=abs_real_inner_le_norm _ _
      _ ≤ M*(‖S‖*M):=mul_le_mul hv
        ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) (norm_nonneg _) hM
      _=_:=by ring
  calc
    _ ≤ |inner ℝ u (S v)|+|inner ℝ v (S u)|+|inner ℝ v (S v)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖S‖*M*‖u‖+‖S‖*M*‖u‖+‖S‖*M^2 := add_le_add (add_le_add h1 h2) h3
    _=_:=by ring

/-- True squared-error transport under a vector translation. The error
uses ordinary second moments, not an assumed Gaussian approximation. -/
theorem quadratic_translation_mean_square (μ : Measure E) [IsProbabilityMeasure μ]
    (S : E →L[ℝ] E) (v : E) {M : ℝ} (hM : 0 ≤ M) (hv : ‖v‖ ≤ M) (t : ℝ)
    (hQ : Integrable (fun u=>(inner ℝ u (S u)-t)^2) μ)
    (hU : Integrable (fun u:E=>‖u‖^2) μ) :
    Integrable (fun u=>(inner ℝ (u+v) (S (u+v))-t)^2) μ ∧
      (∫ u,(inner ℝ (u+v) (S (u+v))-t)^2 ∂μ) ≤
        2*(∫ u,(inner ℝ u (S u)-t)^2 ∂μ)+
          16*‖S‖^2*M^2*(∫ u,‖u‖^2 ∂μ)+4*‖S‖^2*M^4 := by
  let F:=fun u:E=>inner ℝ (u+v) (S (u+v))-t
  let G:=fun u:E=>inner ℝ u (S u)-t
  let R:=fun u:E=>2*G u^2+16*‖S‖^2*M^2*‖u‖^2+4*‖S‖^2*M^4
  have hR : Integrable R μ:=((hQ.const_mul 2).add (hU.const_mul (16*‖S‖^2*M^2))).add (integrable_const _)
  have hp (u:E) : F u^2 ≤ R u := by
    have hab:=quadratic_translation_abs_le S u v hM hv
    have hd : (F u-G u)^2 ≤ (‖S‖*M*(2*‖u‖+M))^2 := by
      have hh:=(sq_le_sq₀ (abs_nonneg _) (show 0 ≤ ‖S‖*M*(2*‖u‖+M) by positivity)).mpr hab
      simpa only [sq_abs,F,G,sub_sub_sub_cancel_right] using hh
    have haux : (2*‖u‖+M)^2 ≤ 8*‖u‖^2+2*M^2 := by nlinarith [sq_nonneg (2*‖u‖-M)]
    have hd' : (F u-G u)^2 ≤ 8*‖S‖^2*M^2*‖u‖^2+2*‖S‖^2*M^4 := by
      calc
        _ ≤ (‖S‖*M)^2*(2*‖u‖+M)^2:=by simpa only [mul_pow] using hd
        _ ≤ (‖S‖*M)^2*(8*‖u‖^2+2*M^2):=mul_le_mul_of_nonneg_left haux (sq_nonneg _)
        _=_:=by ring
    dsimp only [R]
    nlinarith [sq_nonneg (F u-2*G u)]
  have hF : Integrable (fun u=>F u^2) μ:=hR.mono' (by fun_prop) (ae_of_all _ (fun u=>by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hp u))
  refine ⟨hF,?_⟩
  have hh:=integral_mono_ae hF hR (ae_of_all _ hp)
  change (∫ u,F u^2 ∂μ) ≤ _
  calc
    _ ≤ ∫ u,R u ∂μ:=hh
    _=_:=by
      dsimp only [R,G]
      have hAdd1 : (∫ u,2*(inner ℝ u (S u)-t)^2+16*‖S‖^2*M^2*‖u‖^2+4*‖S‖^2*M^4 ∂μ)=
          (∫ u,2*(inner ℝ u (S u)-t)^2+16*‖S‖^2*M^2*‖u‖^2 ∂μ)+(∫ _u:E,4*‖S‖^2*M^4 ∂μ) := by
        convert integral_add ((hQ.const_mul 2).add (hU.const_mul (16*‖S‖^2*M^2)))
          (integrable_const (4*‖S‖^2*M^4)) using 1
      have hAdd2 : (∫ u,2*(inner ℝ u (S u)-t)^2+16*‖S‖^2*M^2*‖u‖^2 ∂μ)=
          (∫ u,2*(inner ℝ u (S u)-t)^2 ∂μ)+(∫ u,16*‖S‖^2*M^2*‖u‖^2 ∂μ) := by
        convert integral_add (hQ.const_mul 2) (hU.const_mul (16*‖S‖^2*M^2)) using 1
      rw [hAdd1,hAdd2,integral_const_mul,integral_const_mul,integral_const,probReal_univ,one_smul]

end
end SlowEquilibration.GaussianQuadraticVariance

