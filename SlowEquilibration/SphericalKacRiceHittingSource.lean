-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalRealTimePathKernel
public import SlowEquilibration.SphericalFullFieldSphereTV
public import SlowEquilibration.SphericalParisiContinuousMaximum

/-! # Source Lemma 7.21: field-dependent diffusion hitting weights

The full polynomial field is the source parameter.  The path space is
literally `C([0,T],S_N)`, with real (not nonnegative-real) time coordinates.
The uniform starting law is the physical radius-`sqrt N` sphere law.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalKacRiceHittingSource

open Set MeasureTheory ProbabilityTheory SphericalModel SphericalFieldKernels
open SphericalRotationCovariance
open SphericalRealTimePathKernel SphericalFullFieldSphereTV
open SphericalParisiContinuousMaximum SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal RealInnerProductSpace

variable {N : ℕ}
set_option maxHeartbeats 1200000

instance realPathTime_nonempty (T : ℝ≥0) : Nonempty (RealPathTime T) :=
  ⟨⟨0, ⟨le_refl _, T.property⟩⟩⟩

/-- The subtype recovery used by the path kernel has precisely the original
uniform sphere measure as its ambient image. -/
theorem uniformInitial_ambient_image (hN : 2 ≤ N) :
    ((sphereLaw N).map (sphereStateRecovery (sphereBasepoint (by omega : 1 ≤ N)))).map
      Subtype.val = sphereLaw N := by
  rw [Measure.map_map measurable_subtype_coe (sphereStateRecovery_measurable _)]
  conv_rhs => rw [← Measure.map_id (μ := sphereLaw N)]
  apply Measure.map_congr
  filter_upwards [sphereLaw_support (by omega : 1 ≤ N)] with x hx
  have hs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  simp [sphereStateRecovery, hs]

/-- The physical path kernel, with an ambient initial point recovered on the
sphere.  The recovery changes only points outside the support of `sphereLaw`. -/
def ambientStartPathKernel (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Field N μ × Vector N) (RealSpherePath N T) :=
  (realPathKernel μ β T).comap
    (fun q => (q.1, sphereStateRecovery (sphereBasepoint (by omega : 1 ≤ N)) q.2))
    (measurable_fst.prodMk
      ((sphereStateRecovery_measurable (sphereBasepoint (by omega : 1 ≤ N))).comp
        measurable_snd))

instance ambientStartPathKernel_markov (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (T : ℝ≥0) : IsMarkovKernel (ambientStartPathKernel hN μ β T) := by
  unfold ambientStartPathKernel
  infer_instance

/-- The law `P^H_{ν_N}`: first draw the actual uniform sphere point, then run
the actual field-dependent diffusion path kernel. -/
def uniformRealPathKernel (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Field N μ) (RealSpherePath N T) :=
  (ambientStartPathKernel hN μ β T) ∘ₖ
    ((Kernel.id : Kernel (Field N μ) (Field N μ)) ×ₖ
      Kernel.const (Field N μ) (sphereLaw N))

instance uniformRealPathKernel_markov (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (T : ℝ≥0) : IsMarkovKernel (uniformRealPathKernel hN μ β T) := by
  unfold uniformRealPathKernel
  let _ := sphereLaw_probability N
  infer_instance

/-- The arbitrary Borel path-event probability is Borel in the full source
field. -/
theorem pathEventProbability_measurable (hN : 2 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) {A : Set (RealSpherePath N T)} (hA : MeasurableSet A) :
    Measurable (fun H : Field N μ => (uniformRealPathKernel hN μ β T H).real A) :=
  ((uniformRealPathKernel hN μ β T).measurable_coe hA).ennreal_toReal

/-- A source field-dependent weight for any Borel set in
`C([0,T],S_N) × S_N`. -/
def pathPointWeight (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (A : Set (RealSpherePath N T × PhysicalSphere N))
    (q : Field N μ × PhysicalSphere N) : ℝ :=
  let κ : Kernel (Field N μ × PhysicalSphere N) (RealSpherePath N T) :=
    (uniformRealPathKernel hN μ β T).comap Prod.fst measurable_fst
  (κ q).real
    (Prod.mk q ⁻¹' {z : (Field N μ × PhysicalSphere N) × RealSpherePath N T |
      (z.2, z.1.2) ∈ A})

theorem pathPointWeight_eq (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (T : ℝ≥0) (A : Set (RealSpherePath N T × PhysicalSphere N))
    (q : Field N μ × PhysicalSphere N) :
    pathPointWeight hN μ β T A q =
      (uniformRealPathKernel hN μ β T q.1).real {p | (p, q.2) ∈ A} := by
  dsimp only [pathPointWeight]
  rw [Kernel.comap_apply]
  rfl

/-- Joint Borel measurability of every arbitrary path-point event weight. -/
theorem pathPointWeight_measurable (hN : 2 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) {A : Set (RealSpherePath N T × PhysicalSphere N)}
    (hA : MeasurableSet A) :
    Measurable (pathPointWeight hN μ β T A) := by
  have hE : MeasurableSet
      {z : (Field N μ × PhysicalSphere N) × RealSpherePath N T |
        (z.2, z.1.2) ∈ A} :=
    hA.preimage (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  change Measurable (fun q : Field N μ × PhysicalSphere N =>
    (((uniformRealPathKernel hN μ β T).comap Prod.fst measurable_fst) q).real
      (Prod.mk q ⁻¹' {z : (Field N μ × PhysicalSphere N) × RealSpherePath N T |
        (z.2, z.1.2) ∈ A}))
  exact (Kernel.measurable_kernel_prodMk_left
    (κ := (uniformRealPathKernel hN μ β T).comap Prod.fst measurable_fst)
    hE).ennreal_toReal

theorem pathPointWeight_mem_unit (hN : 2 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (A : Set (RealSpherePath N T × PhysicalSphere N))
    (q : Field N μ × PhysicalSphere N) :
    pathPointWeight hN μ β T A q ∈ Icc (0 : ℝ) 1 :=
  by rw [pathPointWeight_eq]; exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Absolute overlap along the literal real-time sphere-valued path. -/
def realOverlapPath (T : ℝ≥0)
    (z : RealSpherePath N T × PhysicalSphere N) : C(RealPathTime T, ℝ) :=
  ⟨fun t => |overlap (z.1 t).1 z.2.1|,
    (((continuous_subtype_val.comp z.1.continuous).inner continuous_const).div_const
      (N : ℝ)).abs⟩

theorem realOverlapPath_continuous (T : ℝ≥0) :
    Continuous (realOverlapPath (N := N) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hp : Continuous
      (fun z : (RealSpherePath N T × PhysicalSphere N) × RealPathTime T =>
        (z.1.1 z.2).1) :=
    continuous_subtype_val.comp
      (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))
  have hu : Continuous
      (fun z : (RealSpherePath N T × PhysicalSphere N) × RealPathTime T =>
        z.1.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  exact ((hp.inner hu).div_const (N : ℝ)).abs

/-- The manuscript's path supremum, attained on the compact real interval. -/
def realPathMaximumOverlap (T : ℝ≥0)
    (z : RealSpherePath N T × PhysicalSphere N) : ℝ :=
  maximum (realOverlapPath T z)

theorem realPathMaximumOverlap_continuous (T : ℝ≥0) :
    Continuous (realPathMaximumOverlap (N := N) T) :=
  maximum_continuous.comp (realOverlapPath_continuous T)

theorem realPathMaximumOverlap_ge_iff (T : ℝ≥0) (a : ℝ)
    (z : RealSpherePath N T × PhysicalSphere N) :
    a ≤ realPathMaximumOverlap T z ↔
      ∃ t : RealPathTime T, a ≤ |overlap (z.1 t).1 z.2.1| := by
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := maximum_attained (realOverlapPath T z)
    refine ⟨t, ?_⟩
    change a ≤ (realOverlapPath T z) t
    rw [← ht]
    exact ha
  · rintro ⟨t, ht⟩
    exact ht.trans (le_maximum (realOverlapPath T z) t)

def overlapSupEvent (T : ℝ≥0) (a : ℝ) :
    Set (RealSpherePath N T × PhysicalSphere N) :=
  {z | a ≤ realPathMaximumOverlap T z}

theorem overlapSupEvent_measurable (T : ℝ≥0) (a : ℝ) :
    MeasurableSet (overlapSupEvent (N := N) T a) :=
  measurableSet_le measurable_const (realPathMaximumOverlap_continuous T).measurable

theorem overlapSupEvent_eq_hitting (T : ℝ≥0) (a : ℝ) :
    overlapSupEvent (N := N) T a =
      {z | ∃ t : RealPathTime T, a ≤ |overlap (z.1 t).1 z.2.1|} := by
  ext z
  exact realPathMaximumOverlap_ge_iff T a z

/-- Source Lemma 7.21 for the physical overlap-sup event. -/
theorem overlapSupWeight_measurable (hN : 2 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (a : ℝ) :
    Measurable (pathPointWeight hN μ β T (overlapSupEvent T a)) :=
  pathPointWeight_measurable hN μ β T (overlapSupEvent_measurable T a)

theorem overlapSupWeight_mem_unit (hN : 2 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (a : ℝ)
    (q : Field N μ × PhysicalSphere N) :
    pathPointWeight hN μ β T (overlapSupEvent T a) q ∈ Icc (0 : ℝ) 1 :=
  pathPointWeight_mem_unit hN μ β T _ q

/-- The exponential source horizon is an ordinary positive finite time for
each fixed dimension. No bound uniform in the horizon is asserted. -/
theorem exponentialHorizon_overlapSupWeight_measurable (hN : 2 ≤ N)
    (μ : FiniteMixture) (β γ a : ℝ) :
    Measurable (pathPointWeight hN μ β
      ⟨Real.exp (γ * (N : ℝ)), (Real.exp_pos _).le⟩
      (overlapSupEvent ⟨Real.exp (γ * (N : ℝ)), (Real.exp_pos _).le⟩ a)) :=
  overlapSupWeight_measurable hN μ β _ a

end SlowEquilibration.SphericalKacRiceHittingSource
