module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalHaarTransfer

@[expose] public section

/-! # Equal actual expected event mass from every physical initial point

For a Borel graph of rotation-equivariant tests, the true tensor isotropy
and the derived physical-kernel covariance give the source equal-mass
identity. Initial points and arbitrary initial laws are on the sphere;
there is no off-sphere equality hypothesis.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1800000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalOrthogonalHaar
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}
attribute [local irreducible] mixedTransitionKernel

def eventMass (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (q : Disorder N μ.maxDegree × Vector N) : ℝ :=
  (mixedTransitionKernel μ q.1 β t q.2).real (B q.1)

lemma event_section_measurable (μ : FiniteMixture)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (J : Disorder N μ.maxDegree) : MeasurableSet (B J) :=
  (measurable_const.prodMk measurable_id) hB

theorem eventMass_joint_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1}) :
    Measurable (eventMass μ β t B) := by
  classical
  let F : ((Disorder N μ.maxDegree × Vector N) × ℝ≥0) × Vector N → ℝ :=
    fun z => ({q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1}).indicator
      (fun _ => 1) (z.1.1.1,z.2)
  have hF : Measurable F := (measurable_const.indicator hB).comp
    (measurable_fst.fst.fst.prodMk measurable_snd)
  have hm := (mixedTransitionKernel_joint_integral_measurable μ β F hF).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  convert hm using 1
  funext q
  change eventMass μ β t B q=∫ y, F ((q,t),y) ∂mixedTransitionKernel μ q.1 β t q.2
  have he : (fun y => F ((q,t),y))=(B q.1).indicator (fun _ => (1:ℝ)) := by
    funext y
    by_cases hy : y ∈ B q.1 <;> simp [F,hy]
  rw [he,integral_indicator_const 1 (event_section_measurable μ B hB q.1)]
  simp only [eventMass,smul_eq_mul,mul_one]

lemma eventMass_nonneg (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N)) (q : Disorder N μ.maxDegree × Vector N) :
    0 ≤ eventMass μ β t B q := measureReal_nonneg

lemma eventMass_le_one (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N)) (q : Disorder N μ.maxDegree × Vector N) :
    eventMass μ β t B q ≤ 1 := by
  unfold eventMass
  exact measureReal_le_one

lemma eventMass_field_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (x : Vector N) : Measurable (fun J : Disorder N μ.maxDegree => eventMass μ β t B (J,x)) := by
  have hm : Measurable (fun J : Disorder N μ.maxDegree => (J,x)) :=
    measurable_id.prodMk measurable_const
  exact (eventMass_joint_measurable μ β t B hB).comp hm

lemma eventMass_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (x : Vector N) (hx : OnSphere x) :
    eventMass μ β t B (rotatedDisorder U J,U x)=eventMass μ β t B (J,x) := by
  have hpre : U ⁻¹' B (rotatedDisorder U J)=B J := by
    rw [hrot]
    exact U.injective.preimage_image (B J)
  unfold eventMass
  rw [← mixedTransitionKernel_rotation hN μ J β U t x hx,
    map_measureReal_apply U.continuous.measurable (event_section_measurable μ B hB _),hpre]

theorem mean_eventMass_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) (hx : OnSphere x) :
    (∫ J, eventMass μ β t B (J,U x) ∂disorderLaw N μ.maxDegree)=
      ∫ J, eventMass μ β t B (J,x) ∂disorderLaw N μ.maxDegree := by
  have hm := eventMass_field_measurable μ β t B hB (U x)
  have he := integral_map (μ := disorderLaw N μ.maxDegree)
    (rotatedDisorder_measurable (P := μ.maxDegree) U).aemeasurable hm.aestronglyMeasurable
  rw [(rotatedDisorder_hasLaw (P := μ.maxDegree) U).map_eq] at he
  calc
    _ = ∫ J, eventMass μ β t B (rotatedDisorder U J,U x) ∂disorderLaw N μ.maxDegree := he
    _ = _ := integral_congr_ae (.of_forall fun J => eventMass_rotation hN μ β t B hB hrot U J x hx)

theorem mean_eventMass_eq_onSphere (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (x y : Vector N) (hx : OnSphere x) (hy : OnSphere y) :
    (∫ J, eventMass μ β t B (J,x) ∂disorderLaw N μ.maxDegree)=
      ∫ J, eventMass μ β t B (J,y) ∂disorderLaw N μ.maxDegree := by
  have hn : ‖x‖=‖y‖ := by
    have hxx := (onSphere_iff_norm_sq x).mp hx
    have hyy := (onSphere_iff_norm_sq y).mp hy
    nlinarith [norm_nonneg x,norm_nonneg y]
  obtain ⟨g,hg⟩ := exists_orthogonal_map hn
  have hu : Unitary.linearIsometryEquiv g x=y := hg
  have he := mean_eventMass_rotation hN μ β t B hB hrot (Unitary.linearIsometryEquiv g) x hx
  rw [hu] at he
  exact he.symm

lemma evolved_eventMass_eq_integral (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) :
    (mixedTransitionKernel μ J β t ∘ₘ ν).real (B J)=
      ∫ x, eventMass μ β t B (J,x) ∂ν := by
  have hj := event_section_measurable μ B hB J
  rw [Measure.real,Measure.bind_apply hj (mixedTransitionKernel μ J β t).aemeasurable]
  exact (integral_toReal ((mixedTransitionKernel μ J β t).measurable_coe hj).aemeasurable
    (.of_forall fun x => measure_lt_top (mixedTransitionKernel μ J β t x) (B J))).symm

theorem expected_evolved_mass_eq_point (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, OnSphere y) (x : Vector N) (hx : OnSphere x) :
    (∫ J, (mixedTransitionKernel μ J β t ∘ₘ ν).real (B J) ∂disorderLaw N μ.maxDegree)=
      ∫ J, eventMass μ β t B (J,x) ∂disorderLaw N μ.maxDegree := by
  have hi : Integrable (eventMass μ β t B) ((disorderLaw N μ.maxDegree).prod ν) := by
    apply Integrable.of_bound (eventMass_joint_measurable μ β t B hB).aestronglyMeasurable 1
    exact .of_forall fun q => by
      rw [Real.norm_eq_abs,abs_of_nonneg (eventMass_nonneg μ β t B q)]
      exact eventMass_le_one μ β t B q
  simp_rw [evolved_eventMass_eq_integral μ β t B hB]
  rw [integral_integral_swap (f := fun J y => eventMass μ β t B (J,y)) hi]
  calc
    _ = ∫ _, (∫ J, eventMass μ β t B (J,x) ∂disorderLaw N μ.maxDegree) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hν] with y hy
      exact mean_eventMass_eq_onSphere hN μ β t B hB hrot y x hy hx
    _ = _ := by simp

def uniformExpectedEventMass (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N)) : ℝ :=
  ∫ J, (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N).real (B J) ∂disorderLaw N μ.maxDegree

/-- Source red-equal-mass, pointwise for every physical starting point. -/
theorem point_expected_mass_eq_uniform (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (x : Vector N) (hx : OnSphere x) :
    (∫ J, (mixedTransitionKernel μ J β t x).real (B J) ∂disorderLaw N μ.maxDegree)=
      uniformExpectedEventMass μ β t B := by
  exact (expected_evolved_mass_eq_point hN μ β t B hB hrot (sphereLaw N)
    ((sphereLaw_support hN).mono fun y hy => (onSphere_iff_norm_sq y).mpr hy) x hx).symm

/-- Source red-equal-mass for every ordinary prescribed spherical law,
including singular initial laws. -/
theorem initial_expected_mass_eq_uniform (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1})
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J, B (rotatedDisorder U J)=U '' B J)
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, OnSphere x) :
    (∫ J, (mixedTransitionKernel μ J β t ∘ₘ ν).real (B J) ∂disorderLaw N μ.maxDegree)=
      uniformExpectedEventMass μ β t B := by
  obtain ⟨x,hx⟩ := (sphereLaw_support hN).exists
  have hxs := (onSphere_iff_norm_sq x).mpr hx
  exact (expected_evolved_mass_eq_point hN μ β t B hB hrot ν hν x hxs).trans
    (point_expected_mass_eq_uniform hN μ β t B hB hrot x hxs)

end
end SlowEquilibration.SphericalRotationCovariance
