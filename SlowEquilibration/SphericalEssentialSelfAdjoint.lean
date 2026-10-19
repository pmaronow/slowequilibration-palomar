module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalC2ForcingApprox
public import SlowEquilibration.SphericalC2Cutoff
public import SlowEquilibration.SphericalLaplaceIdentification
public import SlowEquilibration.SphericalOperator
public import SlowEquilibration.ResolventCore

@[expose] public section

/-! # Essential self-adjointness of the literal mixed spherical generator -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalPoissonPrimitive
open SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology ContDiff BigOperators
variable {N : ℕ}

/-- Actual Gibbs L² values of genuine ambient smooth functions. -/
def smoothValueLinear (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : smoothCore N →ₗ[ℝ] Lp ℝ 2 (gibbsLaw N β H) where
  toFun f := gibbsToL2 hN β H hH f (smoothCore_contDiff f).continuous
  map_add' f g := gibbsToL2_add hN β H hH f g
    (smoothCore_contDiff f).continuous (smoothCore_contDiff g).continuous
  map_smul' c f := gibbsToL2_smul hN β H hH f (smoothCore_contDiff f).continuous c

abbrev mixedSmoothForcing (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :=
  smoothResolventForcing hN β (fieldOfMixture μ J)
    ((fieldOfMixture_contDiff μ J).of_le (by simp))

/-- Every literal C² forcing belongs to the actual closure of smooth
forcings, by a true compact cutoff and uniform C² convolution approximation. -/
theorem C2Forcing_mem_closure (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) :
    C2Forcing hN μ J β f hf ∈ closure (Set.range (mixedSmoothForcing hN μ J β)) := by
  obtain ⟨g, hg, hgc, hjet⟩ := exists_C2_cutoff f hf
  obtain ⟨q, hq⟩ := exists_smoothForcing_tendsto hN μ J β g hg hgc
  have he : C2Forcing hN μ J β g hg = C2Forcing hN μ J β f hf := by
    apply gibbsToL2_congr
    filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
    obtain ⟨hv, hd, hdd⟩ := hjet x ((onSphere_iff_norm_sq x).mpr hx)
    rw [hv, mixedGenerator_as_jet, mixedGenerator_as_jet, hd, hdd]
  rw [← he]
  exact isClosed_closure.mem_of_tendsto hq (Eventually.of_forall (fun n =>
    subset_closure ⟨q n, rfl⟩))

/-- The literal C² primitive forcing has its proved finite-time endpoint
formula in the actual physical Gibbs Hilbert space. -/
theorem primitive_forcing_L2 (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {T : ℝ} (hT : 0 < T) :
    C2Forcing hN μ J β (primitive μ J β f T) (primitive_contDiff μ J β hf hfc T) =
      (show Lp ℝ 2 (mixtureGibbsLaw μ β J) from
        gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous) -
        Real.exp (-T) • SphericalL2Semigroup.P hN μ J β T.toNNReal
          (gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous) := by
  have hp : gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous
      (realExpectation μ J β f T) (realExpectation_contDiff μ J β hf hfc T).continuous =
      SphericalL2Semigroup.P hN μ J β T.toNNReal
        (gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous) :=
    SphericalLaplaceIdentification.trajectory_L2 hN μ J β f hf hfc T
  rw [← hp, ← gibbsToL2_smul, ← gibbsToL2_sub]
  apply gibbsToL2_congr
  filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
  exact primitive_forcing (by omega) μ J β hf hfc hT x ((onSphere_iff_norm_sq x).mpr hx)

/-- Every actual compact smooth test lies in the closure of the literal
smooth forcing range. The physical contraction controls the finite-time tail. -/
theorem compact_smooth_mem_forcing_closure (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous ∈
      closure (Set.range (mixedSmoothForcing hN μ J β)) := by
  let U : Lp ℝ 2 (mixtureGibbsLaw μ β J) := gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous
  let z : ℕ → Lp ℝ 2 (mixtureGibbsLaw μ β J) := fun n =>
    U - Real.exp (-((n:ℝ)+1)) • SphericalL2Semigroup.P hN μ J β ((n:ℝ)+1).toNNReal U
  have ht₀ : Tendsto (fun n : ℕ => Real.exp (-((n:ℝ)+1))) atTop (𝓝 (0:ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have ht : Tendsto z atTop (𝓝 U) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by
      simpa only [zero_mul] using ht₀.mul_const ‖U‖)
    dsimp [z]
    rw [sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (SphericalL2Semigroup.P_apply_norm_le hN μ J β _ U) (Real.exp_pos _).le
  apply isClosed_closure.mem_of_tendsto ht
  apply Eventually.of_forall
  intro n
  rw [show z n = C2Forcing hN μ J β (primitive μ J β f ((n:ℝ)+1))
      (primitive_contDiff μ J β (hf.of_le (by simp)) hfc _) from
    (primitive_forcing_L2 hN μ J β f (hf.of_le (by simp)) hfc (by positivity)).symm]
  exact C2Forcing_mem_closure hN μ J β _ (primitive_contDiff μ J β (hf.of_le (by simp)) hfc _)

/-- Density of the literal `(1−L)` smooth forcing is a conclusion of the
actual backward equation, physical contraction, true C² cutoff and mollification. -/
theorem mixedSmoothForcing_dense (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) : DenseRange (mixedSmoothForcing hN μ J β) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro U
  refine (SphericalL2Semigroup.smoothCore_dense hN μ J β).induction
    (P := fun V => V ∈ closure (Set.range (mixedSmoothForcing hN μ J β)))
    ?_ isClosed_closure U
  rintro V ⟨f, hVf, hfc, hf⟩
  have he : V = gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous f hf.continuous := by
    apply Lp.ext
    exact hVf.trans (gibbsToL2_coe hN β (fieldOfMixture μ J)
      (fieldOfMixture_contDiff μ J).continuous f hf.continuous).symm
  rw [he]
  exact compact_smooth_mem_forcing_closure hN μ J β f hf hfc

/-- The actual ambient smooth spherical functions are a genuine operator
core for the proved self-adjoint nonnegative mixed Gibbs generator. -/
theorem mixed_sphericalGenerator_hasCore (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    (sphericalGenerator hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous).HasCore
      (LinearMap.range (smoothValueLinear hN β (fieldOfMixture μ J)
        (fieldOfMixture_contDiff μ J).continuous)) := by
  apply ResolventOperator.inverseShift_hasCore_of_dense_forcing
    (sphericalL2Resolvent hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous)
    (sphericalL2Resolvent_injective hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous)
    (sphericalL2Resolvent_symmetric hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous)
    _ (mixedSmoothForcing hN μ J β)
  · intro f
    exact sphericalL2Resolvent_smoothForcing hN β (fieldOfMixture μ J)
      ((fieldOfMixture_contDiff μ J).of_le (by simp)) f
  · exact mixedSmoothForcing_dense hN μ J β

/-- The literal spherical differential operator on the actual smooth L²
value domain. Its differential action is proved below. -/
def mixedSmoothDifferentialOperator (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    Lp ℝ 2 (mixtureGibbsLaw μ β J) →ₗ.[ℝ] Lp ℝ 2 (mixtureGibbsLaw μ β J) :=
  (sphericalGenerator hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous).domRestrict
    (LinearMap.range (smoothValueLinear hN β (fieldOfMixture μ J)
      (fieldOfMixture_contDiff μ J).continuous))

theorem mixedSmoothDifferentialOperator_domain (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    (mixedSmoothDifferentialOperator hN μ J β).domain =
      LinearMap.range (smoothValueLinear hN β (fieldOfMixture μ J)
        (fieldOfMixture_contDiff μ J).continuous) := by
  exact inf_eq_left.mpr (mixed_sphericalGenerator_hasCore hN μ J β).le_domain

/-- Every actual smooth representative has precisely the literal negative
physical drift/noise generator as its differential operator value. -/
theorem mixedSmoothDifferentialOperator_apply (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (g : smoothCore N) :
    ∃ hg : smoothValueLinear hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous g ∈
        (mixedSmoothDifferentialOperator hN μ J β).domain,
      mixedSmoothDifferentialOperator hN μ J β
        ⟨smoothValueLinear hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous g, hg⟩ =
      -gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous
        (mixedGenerator μ J β g)
        (Ito.generator_continuous β _ (mixedGradient_contDiff μ J)
          ((smoothCore_contDiff g).of_le (by simp))) := by
  obtain ⟨hg, hA⟩ := sphericalGenerator_smooth hN β (fieldOfMixture μ J)
    ((fieldOfMixture_contDiff μ J).of_le (by simp)) g
  refine ⟨⟨⟨g, rfl⟩, hg⟩, ?_⟩
  rw [show mixedSmoothDifferentialOperator hN μ J β
      ⟨smoothValueLinear hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous g,
        ⟨⟨g, rfl⟩, hg⟩⟩ =
      sphericalGenerator hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous
        ⟨gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous g
          (smoothCore_contDiff g).continuous, hg⟩ from rfl, hA]
  congr 1
  apply gibbsToL2_congr
  filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
  exact (mixedGenerator_eq_rotationGenerator (by omega) μ J β
    ((smoothCore_contDiff g).of_le (by simp)) x ((onSphere_iff_norm_sq x).mpr hx)).symm

/-- The actual smooth differential operator closes to the independently
constructed actual self-adjoint weak-form generator. -/
theorem mixedSmoothDifferentialOperator_closure (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    (mixedSmoothDifferentialOperator hN μ J β).closure =
      sphericalGenerator hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous :=
  (mixed_sphericalGenerator_hasCore hN μ J β).closure_eq

/-- Essential self-adjointness of the literal mixed spherical differential
operator: its actual smooth-domain closure is genuinely self-adjoint. -/
theorem mixedSmoothDifferentialOperator_essentiallySelfAdjoint (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    IsSelfAdjoint (mixedSmoothDifferentialOperator hN μ J β).closure := by
  rw [mixedSmoothDifferentialOperator_closure]
  exact sphericalGenerator_selfAdjoint hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous

end
end SlowEquilibration.SphericalForm
