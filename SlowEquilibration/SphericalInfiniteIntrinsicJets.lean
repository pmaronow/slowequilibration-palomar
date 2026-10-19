-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphereWithinHessian
public import SlowEquilibration.SphericalInfiniteIntrinsic

/-! Intrinsic gradient and Hessian bounds for the actual infinite series on
its actual round sphere. Both are derived from the proved within-ball jets. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set MeasureTheory SphericalModel SphericalForm SphereHessian SphericalIntrinsicExtension
open SphericalAging.HardSphereDynamics
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem sphere_mem_physicalBall {n : ℕ} {x : Vector (n+1)} (hx : OnSphere x) :
    x∈physicalBallSet (n+1) := by
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_eq ((Real.sqrt_sq (norm_nonneg _)).symm.trans
    (congrArg Real.sqrt ((onSphere_iff_norm_sq x).mp hx)))

private theorem regularAmbientField_eq_of_sphere (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    (x : Vector (n+1)) (hx : OnSphere x) : regularAmbientField n μ J x=field μ J x := by
  rw [regularAmbientField,ite_eq_left hJ]
  exact ambientExtension_restrict n (intrinsicField n μ J)
    ⟨x,(onSphere_iff_norm_sq x).mp hx⟩

theorem infinite_surfaceGradient_eq_jet (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    (x : Vector (n+1)) (hx : OnSphere x) :
    surfaceGradient (regularAmbientField n μ J) x=withinGradient (firstJetSeries μ J) x := by
  exact surfaceGradient_eq_within (by omega) (field μ J) _ (firstJetSeries μ J) x hx
    (field_hasFDerivWithinAt (by omega) μ J hJ x (sphere_mem_physicalBall hx))
    ((regularAmbientField_contDiff n μ J).differentiable (by norm_num) x)
    (fun y hy => (regularAmbientField_eq_of_sphere n μ J hJ y hy).symm)

theorem infinite_intrinsicHessian_eq_jet (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    (x : Vector (n+1)) (hx : OnSphere x) (v : tangentPlane x) :
    (intrinsicHessian (regularAmbientField n μ J) x v : Vector (n+1))=
      tangentProjection x ((InnerProductSpace.toDual ℝ (Vector (n+1))).symm
        (secondJetSeries μ J x v)) - (firstJetSeries μ J x x/(n+1:ℕ)) • (v : Vector (n+1)) := by
  exact intrinsicHessian_eq_within (by omega) (field μ J) _
    (regularAmbientField_contDiff n μ J) (firstJetSeries μ J) (secondJetSeries μ J)
    (fun y hy => field_hasFDerivWithinAt (by omega) μ J hJ y (sphere_mem_physicalBall hy))
    (fun y hy => firstJetSeries_hasFDerivWithinAt (by omega) μ J hJ y (sphere_mem_physicalBall hy))
    (fun y hy => (regularAmbientField_eq_of_sphere n μ J hJ y hy).symm) x hx v

theorem infinite_surfaceGradient_norm_le (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    (x : Vector (n+1)) (hx : OnSphere x) :
    ‖surfaceGradient (regularAmbientField n μ J) x‖ ≤ fullJetEnvelope μ 1 J := by
  rw [infinite_surfaceGradient_eq_jet n μ J hJ x hx]
  apply (withinGradient_norm_le (by omega) _ x hx).trans
  rw [← field_fderivWithin_eq (by omega) μ J hJ x (sphere_mem_physicalBall hx)]
  exact field_fderivWithin_norm_le (by omega) μ J hJ x (sphere_mem_physicalBall hx)

theorem infinite_intrinsicHessian_norm_le (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    (x : Vector (n+1)) (hx : OnSphere x) :
    ‖intrinsicHessian (regularAmbientField n μ J) x‖ ≤
      fullJetEnvelope μ 2 J+fullJetEnvelope μ 1 J/Real.sqrt (n+1:ℕ) := by
  apply (intrinsicHessian_norm_le_within (by omega) (field μ J) _
    (regularAmbientField_contDiff n μ J) (firstJetSeries μ J) (secondJetSeries μ J)
    (fun y hy => field_hasFDerivWithinAt (by omega) μ J hJ y (sphere_mem_physicalBall hy))
    (fun y hy => firstJetSeries_hasFDerivWithinAt (by omega) μ J hJ y (sphere_mem_physicalBall hy))
    (fun y hy => (regularAmbientField_eq_of_sphere n μ J hJ y hy).symm) x hx).trans
  apply add_le_add
  · rw [← field_second_fderivWithin_eq (by omega) μ J hJ x (sphere_mem_physicalBall hx)]
    exact field_second_fderivWithin_norm_le (by omega) μ J hJ x (sphere_mem_physicalBall hx)
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [← field_fderivWithin_eq (by omega) μ J hJ x (sphere_mem_physicalBall hx)]
    exact field_fderivWithin_norm_le (by omega) μ J hJ x (sphere_mem_physicalBall hx)

/-- The literal intrinsic gradient of the original infinite restricted field
is controlled by the same actual first-jet envelope. -/
theorem infinite_intrinsicGradient_norm_le (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (x : RoundSphere n) :
    ‖intrinsicGradient n (intrinsicField n μ J) x‖ ≤ fullJetEnvelope μ 1 J := by
  have he : regularAmbientField n μ J=ambientExtension n (intrinsicField n μ J) := ite_eq_left hJ
  simpa only [he,intrinsicGradient] using infinite_surfaceGradient_norm_le n μ J hJ x
    ((onSphere_iff_norm_sq _).mpr x.property)

/-- One pair of dimension-independent constants controls both the ambient
closed-ball jets and the genuine intrinsic gradient/Hessian, on a Borel event
under the original infinite disorder law. -/
theorem exists_uniform_intrinsicJet_constants (μ : InfiniteMixture) :
    ∃ K c : ℝ,0<K ∧ 0<c ∧ ∀ n : ℕ,
      ∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
        disorderLaw (n+1) Ωᶜ ≤ ENNReal.ofReal (4*Real.exp (-c*(n+1:ℕ))) ∧
        ∀ J∈Ω,J∈summableJetDisorder μ ∧
          (∀ x∈physicalBallSet (n+1),
            ‖field μ J x‖ ≤ K*(n+1:ℕ) ∧
            ‖fderivWithin ℝ (field μ J) (physicalBallSet (n+1)) x‖ ≤ K*Real.sqrt (n+1:ℕ) ∧
            ‖fderivWithin ℝ (fun y => fderivWithin ℝ (field μ J) (physicalBallSet (n+1)) y)
              (physicalBallSet (n+1)) x‖ ≤ K) ∧
          ∀ x : RoundSphere n,
            ‖intrinsicGradient n (intrinsicField n μ J) x‖ ≤ K*Real.sqrt (n+1:ℕ) ∧
            ‖intrinsicHessian (ambientExtension n (intrinsicField n μ J)) (x : Vector (n+1))‖ ≤ K := by
  classical
  obtain ⟨K,c,hK,hc,hprob⟩ := exists_threeJetEnvelope_constants μ
  refine ⟨2*K,c,by positivity,hc,?_⟩
  intro n
  obtain ⟨R,hR,hRm,hRg⟩ := (summableJetDisorder_ae (N := n+1) (by omega) μ).exists_measurable_mem
  let E : Set (Disorder (n+1)) := {J | ∀ j : Fin 3,fullJetEnvelope μ j.val J ≤ K*jetScale (n+1) j.val}
  have hEm : MeasurableSet E := by
    change MeasurableSet {J | ∀ j : Fin 3,fullJetEnvelope μ j.val J ≤ K*jetScale (n+1) j.val}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le
      (fullJetEnvelope_measurable (by omega) μ j.val) measurable_const
  refine ⟨R∩E,hRm.inter hEm,?_,?_⟩
  · apply (measure_mono_ae ?_).trans (hprob (n+1) (by omega))
    filter_upwards [hR] with J hJR
    intro hbad
    by_contra hnone
    apply hbad
    refine ⟨hJR,?_⟩
    simpa only [E,mem_ofPred_eq,not_exists,not_lt] using hnone
  · intro J hJE
    have hJ := hRg J hJE.1
    have hg := hJE.2
    change ∀ j : Fin 3,fullJetEnvelope μ j.val J ≤ K*jetScale (n+1) j.val at hg
    have hg0 := hg 0
    have hg1 := hg 1
    have hg2 := hg ⟨2,by decide⟩
    simp only [Fin.val_zero,jetScale_zero] at hg0
    simp only [Fin.val_one,jetScale_one] at hg1
    simp only [jetScale_two,mul_one] at hg2
    have hK2 : K≤2*K := by linarith
    have hs : 0<Real.sqrt (n+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨hJ,?_,?_⟩
    · intro x hx
      refine ⟨?_,?_,?_⟩
      · exact ((field_norm_le_fullJetEnvelope (by omega) μ J hJ x
          (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)).trans hg0).trans
          (mul_le_mul_of_nonneg_right hK2 (by positivity))
      · exact ((field_fderivWithin_norm_le (by omega) μ J hJ x hx).trans hg1).trans
          (mul_le_mul_of_nonneg_right hK2 hs.le)
      · exact ((field_second_fderivWithin_norm_le (by omega) μ J hJ x hx).trans hg2).trans hK2
    · intro x
      refine ⟨((infinite_intrinsicGradient_norm_le n μ J hJ x).trans hg1).trans
        (mul_le_mul_of_nonneg_right hK2 hs.le),?_⟩
      have he : regularAmbientField n μ J=ambientExtension n (intrinsicField n μ J) := ite_eq_left hJ
      have hh := infinite_intrinsicHessian_norm_le n μ J hJ x
        ((onSphere_iff_norm_sq _).mpr x.property)
      rw [he] at hh
      apply hh.trans
      have hd : fullJetEnvelope μ 1 J/Real.sqrt (n+1:ℕ) ≤ K := (div_le_iff₀ hs).mpr hg1
      linarith

end SlowEquilibration.SphericalInfiniteModel
