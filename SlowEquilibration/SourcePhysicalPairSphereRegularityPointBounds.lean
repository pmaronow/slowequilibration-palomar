-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereGeodesic

/-! Literal D_N controls the covariant cubic operator at each actual
round-sphere point. Compactness supplies the real suprema; no ordered
tensor event is used in this deterministic selected-event consequence. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set SphericalModel SphericalGaussianJet SphericalForm
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceSphereNormSup {N:ℕ} {F:Type*} [NormedAddCommGroup F] (f:Vector N→F):ℝ:=
  sSup ((fun x=>‖f x‖) '' {x:Vector N|‖x‖^2=(N:ℝ)})

lemma sourceSphereNormSup_nonneg {N:ℕ} {F:Type*} [NormedAddCommGroup F]
    (hN:0<N) (f:Vector N→F) (hf:Continuous f) :0 ≤ sourceSphereNormSup f:=by
  obtain ⟨x,hx⟩:=sourceSphere_nonempty hN
  have hB:=((sourceSphere_compact N).image hf.norm).bddAbove
  exact (norm_nonneg (f x)).trans (le_csSup hB ⟨x,hx,rfl⟩)

lemma sourceSphereNormSup_point_bound {N:ℕ} {F:Type*} [NormedAddCommGroup F]
    (f:Vector N→F) (hf:Continuous f) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    ‖f x‖ ≤ sourceSphereNormSup f:=by
  exact le_csSup ((sourceSphere_compact N).image hf.norm).bddAbove ⟨x,hx,rfl⟩

theorem sourceSphereRegularity_third_point_bound {N P:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (J:Disorder N P) {C:ℝ} (hC:sourceSphereRegularity c J ≤ C)
    (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    ‖sourceSphereThirdExtension c J x‖ ≤ C/Real.sqrt (N:ℝ):=by
  have h0:Continuous (field c J):=(field_contDiff c J).continuous
  have h1:Continuous (surfaceGradient (field c J)):=by
    simpa only [Function.comp_def,id_eq] using
      (source_surfaceGradient_joint_contDiff c).continuous.comp (continuous_const.prodMk continuous_id)
  have h2:Continuous (sourceSphereHessianExtension c J):=(sourceSphereHessianExtension_contDiff c J).continuous
  have h3:Continuous (sourceSphereThirdExtension c J):=by
    simpa only [Function.comp_def,id_eq] using
      (sourceSphereThirdExtension_joint_contDiff c).continuous.comp (continuous_const.prodMk continuous_id)
  have h0n:=sourceSphereNormSup_nonneg hN _ h0
  have h1n:=sourceSphereNormSup_nonneg hN _ h1
  have h2n:=sourceSphereNormSup_nonneg hN _ h2
  have hNr:(0:ℝ)<N:=Nat.cast_pos.mpr hN
  have hs:0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr hNr
  have hreg:sourceSphereRegularity c J=
      sourceSphereNormSup (field c J)/(N:ℝ)+sourceSphereNormSup (surfaceGradient (field c J))/Real.sqrt (N:ℝ)+
        sourceSphereNormSup (sourceSphereHessianExtension c J)+
          Real.sqrt (N:ℝ)*sourceSphereNormSup (sourceSphereThirdExtension c J):=by
    unfold sourceSphereRegularity sourceSphereNormSup
    simp only [Real.norm_eq_abs]
  have hsum:Real.sqrt (N:ℝ)*sourceSphereNormSup (sourceSphereThirdExtension c J) ≤ C:=by
    rw [hreg] at hC
    linarith [div_nonneg h0n hNr.le,div_nonneg h1n hs.le]
  have hp:=sourceSphereNormSup_point_bound (sourceSphereThirdExtension c J) h3 x hx
  apply (le_div_iff₀ hs).mpr
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hp hs.le).trans hsum

end
end SlowEquilibration.PairConditionalDeterminantMoments
