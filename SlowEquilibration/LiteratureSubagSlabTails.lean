-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagLemma22
public import SlowEquilibration.SourceMainTheoremsChenLower
public import SlowEquilibration.LiteratureSubagTheorem10Proof2
public import SlowEquilibration.LiteratureSubagResidualReplicatedLimit
public import SlowEquilibration.LiteratureSubagThickLatitudeLower
public import SlowEquilibration.SphericalParisiRadiusConcentration
public import SlowEquilibration.EntranceLatitudeGaussianRadiusNormalization
public import SlowEquilibration.GaussianAffineDeterminantFinite

/-!
The unnormalized orthonormal-frame slab tails in Subag's Lemma 20 follow
from Lemma 22 and convergence of the physical pressure. Restriction retains
the original mixture and its square-root dimension correction. The actual
Gaussian cavity representation thickens the section at bounded distance,
and arbitrary-rate tensor regularity controls the resulting field error.

These tails prove the residual replicated limit and the lower-band
approximation. The literal manuscript endpoints are restated with Chen and
the explicit universal PressureLowerTails hypothesis as their only
literature inputs. The contact ground-profile and gap clauses need Chen alone.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagSlabTails

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagBandLowerComplete LiteratureSubagBandLowerTails
open SphericalTaylorRemainder SphericalGaussianJet WholeFieldRegression
open GaussianContinuousFieldLaw
open SphericalParisiCavityCovariance SphericalParisiCavityReference
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restricting a physical field to a spherical linear section changes
only its amplitude by the square root of the dimension ratio. -/
theorem sphericalSection_continuousField_law
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (μ : FiniteMixture)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (x : K → Vector d) (hx : Continuous x) :
    (disorderLaw N μ.maxDegree).map (fun J =>
      modelContinuousField (mixtureCoefficients μ)
        (fun u => Real.sqrt ((N : ℝ) / (d : ℝ)) • e (x u))
        ((e.continuous.comp hx).const_smul (Real.sqrt ((N : ℝ) / (d : ℝ))))
        (euclideanDisorder J)) =
      (disorderLaw d μ.maxDegree).map (fun J =>
        Real.sqrt ((N : ℝ) / (d : ℝ)) •
          modelContinuousField (mixtureCoefficients μ) x hx (euclideanDisorder J)) := by
  let s := Real.sqrt ((N : ℝ) / (d : ℝ))
  let z := fun u => s • e (x u)
  have hz : Continuous z := (e.continuous.comp hx).const_smul s
  let X := modelContinuousField (mixtureCoefficients μ) z hz
  let Y := s • modelContinuousField (mixtureCoefficients μ) x hx
  have hs : s ^ 2 = (N : ℝ) / (d : ℝ) := Real.sq_sqrt (by positivity)
  have ho (u v : K) : overlap (z u) (z v) = overlap (x u) (x v) := by
    unfold overlap
    dsimp only [z]
    rw [inner_smul_left, inner_smul_right, e.inner_map_map]
    simp only [conj_trivial]
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    calc
      s * (s * inner ℝ (x u) (x v)) / (N : ℝ) =
          s ^ 2 * inner ℝ (x u) (x v) / (N : ℝ) := by ring
      _ = _ := by rw [hs]; field_simp
  have hLaw : (stdGaussian (EuclideanDisorder N μ.maxDegree)).map X =
      (stdGaussian (EuclideanDisorder d μ.maxDegree)).map Y := by
    apply continuous_field_law_eq X Y
    intro u v
    rw [evaluation_feature_inner, evaluation_feature_inner]
    have hX (u : K) : evaluationFeature X u =
        valueObservation (mixtureCoefficients μ) (z u) := rfl
    have hY (u : K) : evaluationFeature Y u =
        s • valueObservation (mixtureCoefficients μ) (x u) := by
      ext g
      rfl
    rw [hX, hX, hY, hY, scalar_coupling_smul,
      value_value_coupling hN _ (mixtureCoefficients_nonnegative μ),
      value_value_coupling hd _ (mixtureCoefficients_nonnegative μ),
      covariancePolynomial_mixture, covariancePolynomial_mixture, ho, hs]
    field_simp
  have hl := congrArg (fun ν => ν.map X) (actual_flattened_gaussian N μ.maxDegree).map_eq
  have hr := congrArg (fun ν => ν.map Y) (actual_flattened_gaussian d μ.maxDegree).map_eq
  rw [Measure.map_map X.continuous.measurable (euclideanDisorder_measurable _ _)] at hl
  rw [Measure.map_map Y.continuous.measurable (euclideanDisorder_measurable _ _)] at hr
  exact hl.trans (hLaw.trans hr.symm)

/-- The normalized surface partition on a linear section. The surface
measure has mass one in the section's own dimension. -/
def sphericalSectionPartition {N d : ℕ} (μ : FiniteMixture) (β : ℝ)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree) : ℝ :=
  partition d β (fun x => fieldOfMixture μ J
    (Real.sqrt ((N : ℝ) / (d : ℝ)) • e x))

/-- The section partition has exactly the law of the original smaller
model at the dimension-corrected temperature. -/
theorem sphericalSection_logPartition_law {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d) (μ : FiniteMixture) (β : ℝ)
    (e : Vector d →ₗᵢ[ℝ] Vector N) :
    (disorderLaw N μ.maxDegree).map (fun J =>
      Real.log (sphericalSectionPartition μ β e J)) =
      (disorderLaw d μ.maxDegree).map (fun J =>
        Real.log (mixturePartition μ
          (β * Real.sqrt ((N : ℝ) / (d : ℝ))) J)) := by
  let K := CompactSphereCarrier.Carrier d
  let ν := CompactSphereCarrier.law d
  let : IsProbabilityMeasure ν := CompactSphereCarrier.law_probability (by omega)
  let x : K → Vector d := Subtype.val
  have hx : Continuous x := continuous_subtype_val
  let s := Real.sqrt ((N : ℝ) / (d : ℝ))
  let X := fun J : Disorder N μ.maxDegree =>
    modelContinuousField (mixtureCoefficients μ) (fun u => s • e (x u))
      ((e.continuous.comp hx).const_smul s) (euclideanDisorder J)
  let Y := fun J : Disorder d μ.maxDegree =>
    s • modelContinuousField (mixtureCoefficients μ) x hx (euclideanDisorder J)
  have hX : Measurable X :=
    (modelContinuousField _ _ _).continuous.measurable.comp (euclideanDisorder_measurable _ _)
  have hY : Measurable Y :=
    ((modelContinuousField _ _ _).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).const_smul s
  have hF : Measurable (ContinuousFieldPartition.logPartition ν β) :=
    ContinuousFieldPartition.logPartition_measurable ν β
  have hlaw := sphericalSection_continuousField_law hN hd μ e x hx
  change (disorderLaw N μ.maxDegree).map X = (disorderLaw d μ.maxDegree).map Y at hlaw
  have h := ContinuousFieldLaw.observable_map_eq _ _ X Y hX hY hlaw
    (ContinuousFieldPartition.logPartition ν β) hF
  have hleft (J : Disorder N μ.maxDegree) :
      ContinuousFieldPartition.logPartition ν β (X J) =
        Real.log (sphericalSectionPartition μ β e J) := by
    have hc : Continuous (fun u : Vector d => fieldOfMixture μ J (s • e u)) := by
      exact (fieldOfMixture_contDiff μ J).continuous.comp (e.continuous.const_smul s)
    have heq : X J = (⟨fun u : K => fieldOfMixture μ J (s • e u),
        hc.comp continuous_subtype_val⟩ : C(K, ℝ)) := by
      ext u
      exact valueObservation_actual _ _ _
    rw [heq, CompactSphereCarrier.logPartition_eq_sphere (by omega) _ _ hc]
    rfl
  have hright (J : Disorder d μ.maxDegree) :
      ContinuousFieldPartition.logPartition ν β (Y J) =
        Real.log (mixturePartition μ (β * s) J) := by
    have hc : Continuous (fun u : Vector d => s * fieldOfMixture μ J u) :=
      (fieldOfMixture_contDiff μ J).continuous.const_mul s
    have heq : Y J = (⟨fun u : K => s * fieldOfMixture μ J u,
        hc.comp continuous_subtype_val⟩ : C(K, ℝ)) := by
      ext u
      change s * valueObservation _ _ (euclideanDisorder J) = _
      rw [valueObservation_actual]
      rfl
    rw [heq, CompactSphereCarrier.logPartition_eq_sphere (by omega) _ _ hc]
    simp only [mixturePartition, partition, ← mul_assoc]
  change (disorderLaw N μ.maxDegree).map (fun J =>
      ContinuousFieldPartition.logPartition ν β (X J)) =
    (disorderLaw d μ.maxDegree).map (fun J =>
      ContinuousFieldPartition.logPartition ν β (Y J)) at h
  simpa only [hleft, hright] using h

private theorem sphericalSection_logPartition_measurable {N d : ℕ}
    (μ : FiniteMixture) (β : ℝ) (e : Vector d →ₗᵢ[ℝ] Vector N) :
    Measurable (fun J => Real.log (sphericalSectionPartition μ β e J)) := by
  have h : Continuous (fun p : Disorder N μ.maxDegree × Vector d =>
      Real.exp (β * fieldOfMixture μ p.1 (Real.sqrt ((N : ℝ) / (d : ℝ)) • e p.2))) := by
    exact Real.continuous_exp.comp (((field_jointContinuous (mixtureCoefficients μ)).comp
      (continuous_fst.prodMk ((e.continuous.comp continuous_snd).const_smul
        (Real.sqrt ((N : ℝ) / (d : ℝ)))))).const_mul β)
  exact h.measurable.stronglyMeasurable.integral_prod_right.measurable.log

/-- Lemma 22 transfers to every finite-codimension spherical section,
uniformly in its deterministic orientation, centered at the ambient mean. -/
theorem sphericalSection_logPartition_lowerTails
    (μ : FiniteMixture) (β F : ℝ) (r : ℕ) (htail : PressureLowerTails μ β)
    (hlimit : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F)) :
    ∀ t c : ℝ, 0 < t → 0 < c → ∀ᶠ n : ℕ in atTop,
      ∀ e : Vector n →ₗᵢ[ℝ] Vector (n + r),
        (disorderLaw (n + r) μ.maxDegree).real
          {J | Real.log (sphericalSectionPartition μ β e J) / ((n + r : ℕ) : ℝ) <
            quenchedPressure (n + r) μ β - t} ≤
          Real.exp (-c * ((n + r : ℕ) : ℝ)) := by
  intro t c ht hc
  have hnear := (hlimit.comp (tendsto_add_atTop_nat r)).eventually
    (gt_mem_nhds (show F < F + t / 2 by linarith))
  filter_upwards [LiteratureSubagLemma22.dimensionCorrected_pressure_lower_tails_of_limit
    μ β F r htail hlimit (t / 2) c (by positivity) hc,
    hnear, eventually_ge_atTop (1 : ℕ)] with n hn hnear hnpos
  intro e
  have hM : (0 : ℝ) < (n + r : ℕ) := Nat.cast_pos.mpr (by omega)
  have hlaw := sphericalSection_logPartition_law (by omega : 0 < n + r)
    (by omega : 0 < n) μ β e
  have hp := congrArg (fun ν : Measure ℝ =>
      ν.real (Iio (((n + r : ℕ) : ℝ) * (F - t / 2)))) hlaw
  have hm : Measurable (fun J : Disorder n μ.maxDegree =>
      Real.log (mixturePartition μ (β * Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ))) J)) :=
    (partition_measurable (mixtureCoefficients μ) _).log
  rw [map_measureReal_apply (sphericalSection_logPartition_measurable μ β e)
      measurableSet_Iio,
    map_measureReal_apply hm measurableSet_Iio] at hp
  have hsub : {J : Disorder (n + r) μ.maxDegree |
      Real.log (sphericalSectionPartition μ β e J) / ((n + r : ℕ) : ℝ) <
        quenchedPressure (n + r) μ β - t} ⊆
      (fun J => Real.log (sphericalSectionPartition μ β e J)) ⁻¹'
        Iio (((n + r : ℕ) : ℝ) * (F - t / 2)) := by
    intro J hJ
    change Real.log (sphericalSectionPartition μ β e J) / ((n + r : ℕ) : ℝ) <
      quenchedPressure (n + r) μ β - t at hJ
    dsimp only [Function.comp_def] at hnear
    change Real.log (sphericalSectionPartition μ β e J) < _
    rw [mul_comm ((n + r : ℕ) : ℝ)]
    apply (div_lt_iff₀ hM).mp
    linarith
  have heq : (fun J : Disorder n μ.maxDegree =>
      Real.log (mixturePartition μ (β * Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ))) J)) ⁻¹'
        Iio (((n + r : ℕ) : ℝ) * (F - t / 2)) =
      {J | Real.log (mixturePartition μ
        (dimensionCorrectedTemperature β r n) J) / ((n + r : ℕ) : ℝ) < F - t / 2} := by
    ext J
    change Real.log (mixturePartition μ
        (dimensionCorrectedTemperature β r n) J) <
      ((n + r : ℕ) : ℝ) * (F - t / 2) ↔
      Real.log (mixturePartition μ (dimensionCorrectedTemperature β r n) J) /
        ((n + r : ℕ) : ℝ) < F - t / 2
    rw [mul_comm ((n + r : ℕ) : ℝ)]
    exact (div_lt_iff₀ hM).symm
  exact (measureReal_mono hsub).trans (hp.trans_le (by rw [heq]; exact hn))

private theorem append_smul {n r : ℕ} (a : ℝ) (x : Vector n) (z : Vector r) :
    a • append x z = append (a • x) (a • z) := by
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

private theorem append_sub {n r : ℕ} (x y : Vector n) (z w : Vector r) :
    append x z - append y w = append (x - y) (z - w) := by
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- A bounded cavity Gaussian and a bulk radius away from zero thicken
the section by a dimension-independent distance. -/
theorem cavityReferenceMap_dist_le {n r : ℕ} (hn : 1 ≤ n) (hr : r ≤ n)
    (x : Vector n) (hx : ‖x‖ ^ 2 = (n : ℝ)) {a : ℝ}
    (ha : Real.sqrt (n : ℝ) / 2 ≤ a) (z : Vector r) (hz : ‖z‖ ≤ 1) :
    dist (cavityReferenceMap n r (x, a, z))
      (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) • append x (0 : Vector r)) ≤ 8 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have ha0 : 0 < a := by linarith
  let v := append ((a / Real.sqrt (n : ℝ)) • x) z
  let w := append ((a / Real.sqrt (n : ℝ)) • x) (0 : Vector r)
  have hw : ‖w‖ = a := by
    apply (sq_eq_sq₀ (norm_nonneg _) ha0.le).mp
    dsimp only [w]
    rw [append_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
      Real.sq_sqrt hn0.le, hx]
    field_simp
  have hv : a ≤ ‖v‖ := by
    apply (sq_le_sq₀ ha0.le (norm_nonneg _)).mp
    have h := append_norm_sq ((a / Real.sqrt (n : ℝ)) • x) z
    have hw' := append_norm_sq ((a / Real.sqrt (n : ℝ)) • x) (0 : Vector r)
    change ‖w‖ ^ 2 = _ at hw'
    rw [hw] at hw'
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at hw'
    change _ ≤ ‖v‖ ^ 2
    change ‖v‖ ^ 2 = _ at h
    simpa using (show a ^ 2 ≤ ‖v‖ ^ 2 by nlinarith [sq_nonneg ‖z‖])
  have hv0 : 0 < ‖v‖ := ha0.trans_le hv
  have hd : dist v w = ‖z‖ := by
    rw [dist_eq_norm]
    dsimp only [v, w]
    rw [append_sub, sub_self, sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [append_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_add]
  have hnrm : SphericalAging.SphereInitialLaw.normalize (n + r) w =
      Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) • append x (0 : Vector r) := by
    rw [SphericalAging.SphereInitialLaw.normalize, hw]
    have hwrep : w = (a / Real.sqrt (n : ℝ)) • append x (0 : Vector r) := by
      rw [append_smul, smul_zero]
    rw [hwrep, smul_smul]
    congr 1
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
    field_simp
  have hroot : Real.sqrt ((n + r : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, Real.sq_sqrt hn0.le]
    have : (r : ℝ) ≤ n := Nat.cast_le.mpr hr
    push_cast
    nlinarith
  have hratio : 2 * Real.sqrt ((n + r : ℕ) : ℝ) / ‖v‖ ≤ 8 := by
    apply (div_le_iff₀ hv0).mpr
    linarith
  have h := EntranceLatitudeGaussianRadius.radial_normalization_dist_le
    (Real.sqrt_nonneg ((n + r : ℕ) : ℝ)) v w hv0 (by rw [hw]; exact ha0)
  rw [hd] at h
  change dist (SphericalAging.SphereInitialLaw.normalize (n + r) v)
      (SphericalAging.SphereInitialLaw.normalize (n + r) w) ≤ _ at h
  rw [hnrm] at h
  exact h.trans ((mul_le_mul hratio hz (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

private theorem exists_frame_rotation {n r : ℕ}
    (e : Fin r → Vector (n + r)) (he : Orthonormal ℝ e) :
    ∃ U : Vector (n + r) ≃ₗᵢ[ℝ] Vector (n + r),
      ∀ i : Fin r, U (EuclideanSpace.single (Fin.natAdd n i) 1) = e i := by
  classical
  let s : Set (Fin (n + r)) := {i | n ≤ i.val}
  let f : s → Fin r := fun i => ⟨i.val.val - n, by
    have hi := i.val.isLt
    have hnle : n ≤ i.val.val := i.property
    omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hi := i.property
    have hj := j.property
    have h := congrArg Fin.val hij
    dsimp [f, s] at *
    omega
  let v : Fin (n + r) → Vector (n + r) := fun i =>
    if h : n ≤ i.val then e ⟨i.val - n, by omega⟩ else 0
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    have hvrep : s.domRestrict v = e ∘ f := by
      funext i
      dsimp only [Set.domRestrict, v, Function.comp_def, f]
      rw [dite_eq_left (show n ≤ i.val.val from i.property)]
    rw [hvrep]
    exact he.comp f hf
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b.repr.symm, ?_⟩
  intro i
  rw [b.repr_symm_single, hb _ (by dsimp [s]; omega)]
  simp only [v, Fin.val_natAdd, le_add_iff_nonneg_right, Nat.zero_le,
    ↓reduceDIte, Nat.add_sub_cancel_left]

private def bulkEmbedding {n r : ℕ}
    (U : Vector (n + r) ≃ₗᵢ[ℝ] Vector (n + r)) : Vector n →ₗᵢ[ℝ] Vector (n + r) where
  toLinearMap :=
    { toFun := fun x => U (append x (0 : Vector r))
      map_add' := by
        intro x y
        rw [← U.map_add]
        congr 1
        apply PiLp.ext
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a x
        rw [← U.map_smul]
        congr 1
        simp only [append_smul, smul_zero, RingHom.id_apply] }
  norm_map' := by
    intro x
    change ‖U (append x (0 : Vector r))‖ = ‖x‖
    rw [U.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [append_norm_sq, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero]

private theorem good_radius_mass_eventually :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤
      (radiusLaw n).real {a | Real.sqrt (n : ℝ) / 2 ≤ a} := by
  have h := SphericalParisiRadiusConcentration.actual_good_radius_probability
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  apply hn.le.trans
  rw [radiusLaw, map_measureReal_apply measurable_norm (by measurability),
    map_measureReal_apply measurable_norm (by measurability)]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro g hg
  change |‖g‖ ^ 2 / (n : ℝ) - 1| < 1 / 2 at hg
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsq := Real.sq_sqrt hn0.le
  have h := (abs_lt.mp hg).1
  have hh := (lt_div_iff₀ hn0).mp (show (1 / 2 : ℝ) < ‖g‖ ^ 2 / (n : ℝ) by linarith)
  change Real.sqrt (n : ℝ) / 2 ≤ ‖g‖
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (n : ℝ)]

private theorem cavity_ball_mass_pos (r : ℕ) :
    0 < (SphericalAging.SphereInitialLaw.gaussianLaw r).real
      (Metric.closedBall (0 : Vector r) 1) := by
  have h := GaussianAffineDeterminant.gaussian_closedBall_real_pos
    (ι := Fin r) (by norm_num : (0 : ℝ) < 1)
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] at h
  exact h

private theorem cavityReferenceMap_norm_sq {n r : ℕ} (hn : 1 ≤ n)
    (x : Vector n) (hx : ‖x‖ ^ 2 = (n : ℝ)) {a : ℝ}
    (ha : Real.sqrt (n : ℝ) / 2 ≤ a) (z : Vector r) :
    ‖cavityReferenceMap n r (x, a, z)‖ ^ 2 = ((n + r : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have ha0 : 0 < a := by have := Real.sqrt_pos.mpr hn0; linarith
  have hv : append ((a / Real.sqrt (n : ℝ)) • x) z ≠ 0 := by
    intro hv
    have h := append_norm_sq ((a / Real.sqrt (n : ℝ)) • x) z
    rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, div_pow, Real.sq_sqrt hn0.le, hx] at h
    have hnz : (n : ℝ) ≠ 0 := hn0.ne'
    rw [div_mul_cancel₀ _ hnz] at h
    nlinarith [sq_nonneg ‖z‖]
  exact SphericalAging.SphereInitialLaw.normalize_norm_sq _ hv

private theorem actual_ball_lipschitz {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) :
    LipschitzOnWith
      ⟨SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant c J,
        SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant_nonneg c J⟩
      (field c J) (Metric.closedBall 0 (Real.sqrt (N : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (field_contDiff c J).differentiable (by simp) x) _
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ)))
  intro x hx
  have hc : Continuous (fun x : Vector N => ‖fderiv ℝ (field c J) x‖) :=
    ((field_contDiff c J).fderiv_right (m := ⊤) (by simp)).continuous.norm
  have hb := ((isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).image hc).bddAbove
  have hle : ‖fderiv ℝ (field c J) x‖ ≤
      SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant c J :=
    le_csSup hb ⟨x, hx, rfl⟩
  exact_mod_cast hle

private theorem fixedSlabPartition_thickening
    (r : ℕ) (β : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (μ : FiniteMixture) (J : Disorder (n + r) μ.maxDegree)
        (e : Fin r → Vector (n + r)), Orthonormal ℝ e →
      ∀ U : Vector (n + r) ≃ₗᵢ[ℝ] Vector (n + r),
        (∀ i : Fin r, U (EuclideanSpace.single (Fin.natAdd n i) 1) = e i) →
      b * Real.exp (-8 * |β| *
          SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant
            (mixtureCoefficients μ) J) *
          sphericalSectionPartition μ β (bulkEmbedding U) J ≤
        fixedSlabPartition μ β η J (fun i => Real.sqrt ((n + r : ℕ) : ℝ) • e i) := by
  let q := (SphericalAging.SphereInitialLaw.gaussianLaw r).real
    (Metric.closedBall (0 : Vector r) 1)
  have hq : 0 < q := cavity_ball_mass_pos r
  refine ⟨q / 2, by positivity, ?_⟩
  have hroot : Tendsto (fun n : ℕ => Real.sqrt ((n + r : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat r))
  filter_upwards [good_radius_mass_eventually, eventually_ge_atTop (max 2 r),
    hroot.eventually_gt_atTop (8 / η)] with n hmass hn hlarge
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hrn : r ≤ n := le_trans (le_max_right _ _) hn
  have hN : 1 ≤ n + r := by omega
  have hR : 0 < Real.sqrt ((n + r : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hwidth : 8 < η * Real.sqrt ((n + r : ℕ) : ℝ) := by
    have := (div_lt_iff₀ hη).mp hlarge
    linarith
  intro μ J e he U hU
  let Q := (radiusLaw n).prod (SphericalAging.SphereInitialLaw.gaussianLaw r)
  let ν := (sphereLaw n).prod Q
  let G : Set (ℝ × Vector r) :=
    {a | Real.sqrt (n : ℝ) / 2 ≤ a} ×ˢ Metric.closedBall (0 : Vector r) 1
  have hG : MeasurableSet G := (measurableSet_le measurable_const measurable_id).prod
    Metric.isClosed_closedBall.measurableSet
  let T : Vector n × ℝ × Vector r → Vector (n + r) :=
    fun p => U (cavityReferenceMap n r p)
  have hTm : Measurable T := U.continuous.measurable.comp (cavityReferenceMap_measurable n r)
  have hTlaw : ν.map T = sphereLaw (n + r) := by
    change ν.map (U ∘ cavityReferenceMap n r) = sphereLaw (n + r)
    dsimp only [ν, Q]
    rw [← Measure.map_map U.continuous.measurable (cavityReferenceMap_measurable n r),
      ← actual_cavity_reference_product hn1, sphereLaw_rotation_invariant]
  have hTmp : MeasurePreserving T ν (sphereLaw (n + r)) := ⟨hTm, hTlaw⟩
  let H := fieldOfMixture μ J
  let S : Set (Vector (n + r)) :=
    {y | ∀ i, |overlap y (Real.sqrt ((n + r : ℕ) : ℝ) • e i)| < η}
  have hS : MeasurableSet S := by
    dsimp only [S]
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_lt (by unfold overlap; fun_prop) measurable_const
  let g : Vector (n + r) → ℝ := S.indicator (fun y => Real.exp (β * H y))
  have hg : Integrable g (sphereLaw (n + r)) :=
    ((partitionAgainst_integrable (sphereLaw (n + r)) (sphereLaw_support hN) β
      (fieldOfMixture_contDiff μ J).continuous).indicator hS)
  have hgi : Integrable (g ∘ T) ν := hTmp.integrable_comp_of_integrable hg
  let A := Real.exp (-8 * |β| *
    SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant
      (mixtureCoefficients μ) J)
  let f : Vector n × ℝ × Vector r → ℝ := fun p =>
    Real.exp (β * H (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) •
      bulkEmbedding U p.1)) * G.indicator (fun _ => A) p.2
  have hsphere : ∀ᵐ p ∂ν, ‖p.1‖ ^ 2 = (n : ℝ) :=
    (measurePreserving_fst (μ := sphereLaw n) (ν := Q)).quasiMeasurePreserving.ae
      (sphereLaw_support hn1)
  have hfg : f ≤ᵐ[ν] g ∘ T := by
    filter_upwards [hsphere] with p hp
    by_cases hgood : p.2 ∈ G
    · have ha : Real.sqrt (n : ℝ) / 2 ≤ p.2.1 := hgood.1
      have hz : ‖p.2.2‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hgood.2
      let y := Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) • bulkEmbedding U p.1
      have hyd : dist (T p) y ≤ 8 := by
        change dist (U (cavityReferenceMap n r p))
          (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) • U (append p.1 0)) ≤ 8
        rw [← U.map_smul, U.dist_map]
        exact cavityReferenceMap_dist_le hn1 hrn p.1 hp ha p.2.2 hz
      have hy : ‖y‖ ^ 2 = ((n + r : ℕ) : ℝ) := by
        dsimp only [y]
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          Real.sq_sqrt (by positivity), (bulkEmbedding U).norm_map, hp]
        exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      have hty : ‖T p‖ ^ 2 = ((n + r : ℕ) : ℝ) := by
        rw [show T p = U (cavityReferenceMap n r p) from rfl, U.norm_map]
        exact cavityReferenceMap_norm_sq hn1 p.1 hp ha p.2.2
      have hyS : T p ∈ S := by
        intro i
        have hzero : inner ℝ y (e i) = 0 := by
          dsimp only [y]
          rw [← hU i, inner_smul_left, conj_trivial]
          change _ * inner ℝ (U (append p.1 0)) (U _) = 0
          rw [U.inner_map_map, EuclideanSpace.inner_single_right]
          simp
        have hnorm : ‖e i‖ = 1 := he.norm_eq_one i
        have hi := abs_real_inner_le_norm (T p - y) (e i)
        rw [inner_sub_left, hzero, sub_zero, hnorm, mul_one] at hi
        have hh : |inner ℝ (T p) (e i)| ≤ 8 :=
          hi.trans (by simpa only [dist_eq_norm] using hyd)
        change |overlap (T p) (Real.sqrt ((n + r : ℕ) : ℝ) • e i)| < η
        unfold overlap
        rw [inner_smul_right, abs_div,
          abs_of_nonneg (Nat.cast_nonneg (n + r) : (0 : ℝ) ≤ (n + r : ℕ)),
          abs_mul, abs_of_nonneg (Real.sqrt_nonneg ((n + r : ℕ) : ℝ))]
        apply (div_lt_iff₀ (Nat.cast_pos.mpr (by omega : 0 < n + r))).mpr
        calc
          _ ≤ Real.sqrt ((n + r : ℕ) : ℝ) * 8 :=
            mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)
          _ < _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg (n + r))]
      have hball {v : Vector (n + r)} (hv : ‖v‖ ^ 2 = ((n + r : ℕ) : ℝ)) :
          v ∈ Metric.closedBall 0 (Real.sqrt ((n + r : ℕ) : ℝ)) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_eq ((Real.sqrt_sq (norm_nonneg v)).symm.trans (congrArg Real.sqrt hv))
      have hlip := (actual_ball_lipschitz (mixtureCoefficients μ) J).dist_le_mul
        (T p) (hball hty) y (hball hy)
      change |H (T p) - H y| ≤
        SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant
          (mixtureCoefficients μ) J * dist (T p) y at hlip
      have hfield : |H (T p) - H y| ≤
          8 * SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant
            (mixtureCoefficients μ) J := by
        exact (show _ ≤ _ from hlip).trans (by
          have := mul_le_mul_of_nonneg_left hyd
            (SourceMixedBandsLiteral.BallLipschitz.physicalBallLipschitzConstant_nonneg
              (mixtureCoefficients μ) J)
          simpa only [mul_comm] using this)
      dsimp only [f, Function.comp_def, g, A]
      rw [indicator_of_mem hgood, indicator_of_mem hyS, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hb := le_abs_self (β * (H y - H (T p)))
      rw [abs_mul, abs_sub_comm (H y)] at hb
      have hm := mul_le_mul_of_nonneg_left hfield (abs_nonneg β)
      nlinarith
    · dsimp only [f]
      rw [indicator_of_notMem hgood, mul_zero]
      exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hcompare := integral_mono_of_nonneg
    (.of_forall fun p => mul_nonneg (Real.exp_pos _).le
      (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)) hgi hfg
  have hfi : (∫ p, f p ∂ν) = sphericalSectionPartition μ β (bulkEmbedding U) J *
      (Q.real G * A) := by
    have hi := integral_prod_mul (μ := sphereLaw n) (ν := Q)
      (fun x : Vector n => Real.exp (β * H
        (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)) • bulkEmbedding U x)))
      (G.indicator (fun _ => A))
    change (∫ p, f p ∂ν) = _ at hi
    rw [hi, integral_indicator hG, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    rfl
  have hgi' : (∫ p, (g ∘ T) p ∂ν) =
      fixedSlabPartition μ β η J (fun i => Real.sqrt ((n + r : ℕ) : ℝ) • e i) := by
    calc
      _ = ∫ y, g y ∂ν.map T :=
        (integral_map hTm.aemeasurable (by rw [hTlaw]; exact hg.aestronglyMeasurable)).symm
      _ = _ := by rw [hTlaw]; exact integral_indicator hS
  rw [hfi, hgi'] at hcompare
  have hmass' : q / 2 ≤ Q.real G := by
    dsimp only [Q, G]
    rw [measureReal_prod_prod]
    change q / 2 ≤ _ * q
    nlinarith
  have hZ : 0 ≤ sphericalSectionPartition μ β (bulkEmbedding U) J :=
    (partition_pos hn1 β ((fieldOfMixture_contDiff μ J).continuous.comp
      ((bulkEmbedding U).continuous.const_smul
        (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)))))).le
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmass' (show 0 ≤ A from (Real.exp_pos _).le)) hZ
  change q / 2 * A * _ ≤ _
  calc
    _ = sphericalSectionPartition μ β (bulkEmbedding U) J * (q / 2 * A) := by ring
    _ ≤ sphericalSectionPartition μ β (bulkEmbedding U) J * (Q.real G * A) := hm
    _ ≤ _ := hcompare

open SourceMixedBandsLiteral.BallLipschitz SphericalAging.GaussianLandscape

private theorem actualBallLipschitz_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (physicalBallLipschitzConstant (N := N) c) := by
  unfold physicalBallLipschitzConstant
  apply (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).continuous_sSup
  exact (PairConditionalDeterminantMoments.source_param_fderiv_contDiff
    (fun J x => field c J x)
    (PairConditionalDeterminantMoments.source_field_joint_contDiff c)).continuous.norm

private theorem actualBallLipschitz_le_envelope {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (J : Disorder N P) :
    physicalBallLipschitzConstant c J ≤
      normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) := by
  unfold physicalBallLipschitzConstant
  apply csSup_le
  · exact ⟨‖fderiv ℝ (field c J) 0‖, 0,
      by simpa only [Metric.mem_closedBall, dist_self] using Real.sqrt_nonneg (N : ℝ), rfl⟩
  · rintro v ⟨x, hx, rfl⟩
    have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hjet := field_iteratedFDeriv_ball_bound
      hN c J x hball 1
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    simp only [pow_one, norm_iteratedFDeriv_one, Nat.descFactorial_one] at hjet
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ (N : ℝ) * normalizedLipschitzEnvelope c J := hjet
      _ = Real.sqrt (N : ℝ) *
          (normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)) := by
        calc
          _ = normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) ^ 2 := by rw [hsq]; ring
          _ = _ := by ring

/-- Lemma 17 with any prescribed exponential rate, for the actual maximum
of the field derivative on the physical ball. The degreewise tensor-net
tails allow the threshold to be chosen before the dimension. -/
private theorem physicalBallLipschitz_arbitrary_rate (μ : FiniteMixture)
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      MeasurableSet {J : Disorder N μ.maxDegree |
        C * Real.sqrt (N : ℝ) <
          physicalBallLipschitzConstant (mixtureCoefficients μ) J} ∧
      (disorderLaw N μ.maxDegree).real
        {J | C * Real.sqrt (N : ℝ) <
          physicalBallLipschitzConstant (mixtureCoefficients μ) J} ≤
        Real.exp (-a * (N : ℝ)) := by
  classical
  let d : ℝ := Fintype.card (Degree μ.maxDegree)
  let r : ℝ := a + d + 2
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr : 1 ≤ r := by dsimp [r]; linarith
  let threshold (p : Degree μ.maxDegree) : ℝ :=
    landscapeThreshold p.val.val + 4 * r
  have hthreshold (p : Degree μ.maxDegree) :
      landscapeThreshold p.val.val ≤ threshold p := by
    dsimp [threshold]; linarith
  have hthresholdpos (p : Degree μ.maxDegree) : 0 < threshold p :=
    (landscapeThreshold_pos _).trans_le (hthreshold p)
  have hthresholdsq (p : Degree μ.maxDegree) : 16 * r ≤ (threshold p) ^ 2 := by
    have hnonneg := (landscapeThreshold_pos p.val.val).le
    have hrr : r ≤ r ^ 2 := by nlinarith
    dsimp [threshold]
    nlinarith [sq_nonneg (landscapeThreshold p.val.val)]
  let C : ℝ := 1 + ∑ p : Degree μ.maxDegree,
    Real.sqrt (mixtureCoefficients μ p) * (p.val.val : ℝ) * threshold p
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ p : Degree μ.maxDegree,
        Real.sqrt (mixtureCoefficients μ p) * (p.val.val : ℝ) * threshold p :=
      Finset.sum_nonneg fun p _ => by
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (hthresholdpos p).le
    dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN
  refine ⟨measurableSet_lt measurable_const
    (actualBallLipschitz_continuous _).measurable, ?_⟩
  let E (p : Degree μ.maxDegree) : Set (Disorder N μ.maxDegree) :=
    {J | threshold p < landscapeNorm N p.val.val (J p)}
  have hsubset : {J : Disorder N μ.maxDegree |
      C * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J}
      ⊆ ⋃ p : Degree μ.maxDegree, E p := by
    intro J hJ
    by_contra hn
    have hbound (p : Degree μ.maxDegree) :
        landscapeNorm N p.val.val (J p) ≤ threshold p := by
      by_contra hp
      exact hn (mem_iUnion.mpr ⟨p, not_le.mp hp⟩)
    have henvelope : normalizedLipschitzEnvelope (mixtureCoefficients μ) J ≤ C := by
      unfold normalizedLipschitzEnvelope
      apply le_trans (Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hbound p)
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)))
      dsimp [C]; linarith
    have hLip := actualBallLipschitz_le_envelope (by omega : 1 ≤ N)
      (mixtureCoefficients μ) J
    have hmul := mul_le_mul_of_nonneg_right henvelope (Real.sqrt_nonneg (N : ℝ))
    exact (not_lt_of_ge (hLip.trans hmul)) hJ
  have htail (p : Degree μ.maxDegree) :
      (disorderLaw N μ.maxDegree).real (E p) ≤
        2 * Real.exp (-(N : ℝ) * r) := by
    have hmeas : MeasurableSet {J : SphericalAging.FiniteModel.Disorder N p.val.val |
        threshold p < landscapeNorm N p.val.val J} :=
      measurableSet_lt measurable_const (landscapeNorm_continuous _ _).measurable
    have hlaw := (degree_block_hasLaw (N := N) p).measureReal_eq hmeas
    change (disorderLaw N μ.maxDegree).real
      {J | threshold p < landscapeNorm N p.val.val (J p)} ≤ _
    rw [hlaw]
    apply (landscape_tail_dimension (by omega : 0 < N)
      (by have hp := p.property; omega : 0 < p.val.val) (hthreshold p)).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left (hthresholdsq p) (Nat.cast_nonneg N)
    nlinarith
  have hsum : (disorderLaw N μ.maxDegree).real
      (⋃ p : Degree μ.maxDegree, E p) ≤
        2 * d * Real.exp (-(N : ℝ) * r) := by
    calc
      _ ≤ ∑ p : Degree μ.maxDegree, (disorderLaw N μ.maxDegree).real (E p) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Degree μ.maxDegree, 2 * Real.exp (-(N : ℝ) * r) :=
        Finset.sum_le_sum fun p _ => htail p
      _ = _ := by simp [d]; ring
  have hcoef : 2 * d ≤ Real.exp (d + 1) := by
    have hde : d ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
    calc
      _ ≤ 2 * Real.exp d := mul_le_mul_of_nonneg_left hde (by norm_num)
      _ ≤ Real.exp 1 * Real.exp d :=
        mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (measureReal_mono hsubset).trans (hsum.trans ?_)
  calc
    _ ≤ Real.exp (d + 1) * Real.exp (-(N : ℝ) * r) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp (d + 1 - (N : ℝ) * r) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-a * (N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hh := mul_le_mul_of_nonneg_left hNr (show 0 ≤ d + 2 by linarith)
      dsimp [r]
      nlinarith


private theorem orthonormalSlabPartitionLowerTails_of_pressure_limit
    (μ : FiniteMixture) (β F : ℝ) (htail : PressureLowerTails μ β)
    (hlimit : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F))
    (r : ℕ) (η t c : ℝ) (hη : 0 < η) (ht : 0 < t) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ e : Fin r → Vector N, Orthonormal ℝ e →
      (disorderLaw N μ.maxDegree).real
        (fixedSlabPartitionLowerTailEvent μ β η t
          (fun i => Real.sqrt (N : ℝ) • e i)) ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨C, hC, hLip⟩ := physicalBallLipschitz_arbitrary_rate μ
    (show 0 < c + 1 by linarith)
  obtain ⟨b, hb, hthick⟩ := fixedSlabPartition_thickening r β hη
  have hnat : Tendsto (fun n : ℕ => ((n + r : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat r)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt ((n + r : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hnat
  have hcost : ∀ᶠ n : ℕ in atTop,
      -Real.log b + 8 * |β| * C * Real.sqrt ((n + r : ℕ) : ℝ) ≤
        t / 2 * ((n + r : ℕ) : ℝ) := by
    filter_upwards [hnat.eventually_ge_atTop (-4 * Real.log b / t),
      hroot.eventually_ge_atTop (32 * |β| * C / t)] with n hn hs
    have hn' := (div_le_iff₀ ht).mp hn
    have hs' := (div_le_iff₀ ht).mp hs
    have hm := mul_le_mul_of_nonneg_right hs' (Real.sqrt_nonneg ((n + r : ℕ) : ℝ))
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (n + r))]
  have hshift : ∀ᶠ n : ℕ in atTop, ∀ e : Fin r → Vector (n + r), Orthonormal ℝ e →
      (disorderLaw (n + r) μ.maxDegree).real
        (fixedSlabPartitionLowerTailEvent μ β η t
          (fun i => Real.sqrt ((n + r : ℕ) : ℝ) • e i)) ≤
        Real.exp (-c * ((n + r : ℕ) : ℝ)) := by
    filter_upwards [hthick, hcost,
      sphericalSection_logPartition_lowerTails μ β F r htail hlimit
        (t / 2) (c + 1) (by positivity) (by linarith),
      eventually_ge_atTop (2 : ℕ)] with n hn hcost hsection hn2
    intro e he
    obtain ⟨U, hU⟩ := exists_frame_rotation e he
    have hN : 2 ≤ n + r := by omega
    have hNr : (0 : ℝ) < (n + r : ℕ) := Nat.cast_pos.mpr (by omega)
    let E := bulkEmbedding U
    let B : Set (Disorder (n + r) μ.maxDegree) :=
      {J | C * Real.sqrt ((n + r : ℕ) : ℝ) <
        physicalBallLipschitzConstant (mixtureCoefficients μ) J}
    let L : Set (Disorder (n + r) μ.maxDegree) :=
      {J | Real.log (sphericalSectionPartition μ β E J) / ((n + r : ℕ) : ℝ) <
        quenchedPressure (n + r) μ β - t / 2}
    have hsub : fixedSlabPartitionLowerTailEvent μ β η t
        (fun i => Real.sqrt ((n + r : ℕ) : ℝ) • e i) ⊆ B ∪ L := by
      intro J hJ
      by_contra hnot
      have hreg : physicalBallLipschitzConstant (mixtureCoefficients μ) J ≤
          C * Real.sqrt ((n + r : ℕ) : ℝ) :=
        le_of_not_gt (fun h => hnot (Or.inl h))
      have hsect : quenchedPressure (n + r) μ β - t / 2 ≤
          Real.log (sphericalSectionPartition μ β E J) / ((n + r : ℕ) : ℝ) :=
        le_of_not_gt (fun h => hnot (Or.inr h))
      have hsect' := (le_div_iff₀ hNr).mp hsect
      have hZpos : 0 < sphericalSectionPartition μ β E J :=
        partition_pos (by omega) β ((fieldOfMixture_contDiff μ J).continuous.comp
          (E.continuous.const_smul (Real.sqrt (((n + r : ℕ) : ℝ) / (n : ℝ)))))
      have hL := mul_le_mul_of_nonneg_left hreg (show 0 ≤ 8 * |β| by positivity)
      have hlow : Real.exp (((n + r : ℕ) : ℝ) * (quenchedPressure (n + r) μ β - t)) ≤
          fixedSlabPartition μ β η J
            (fun i => Real.sqrt ((n + r : ℕ) : ℝ) • e i) := by
        calc
          _ ≤ Real.exp (Real.log b +
              (-8 * |β| * physicalBallLipschitzConstant (mixtureCoefficients μ) J) +
              Real.log (sphericalSectionPartition μ β E J)) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hcost]
          _ = b * Real.exp (-8 * |β| *
              physicalBallLipschitzConstant (mixtureCoefficients μ) J) *
              sphericalSectionPartition μ β E J := by
            rw [Real.exp_add, Real.exp_add, Real.exp_log hb, Real.exp_log hZpos]
          _ ≤ _ := hn μ J e he U hU
      exact (not_lt_of_ge hlow) hJ
    have hprob := (measureReal_mono hsub).trans
      ((measureReal_union_le B L).trans
        (add_le_add (hLip (n + r) hN).2 (hsection E)))
    have htwo : 2 ≤ Real.exp ((n + r : ℕ) : ℝ) := by
      have hdim : (1 : ℝ) ≤ (n + r : ℕ) := by exact_mod_cast (show 1 ≤ n + r by omega)
      exact Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hdim)
    apply hprob.trans
    calc
      _ = 2 * Real.exp (-(c + 1) * ((n + r : ℕ) : ℝ)) := by ring
      _ ≤ Real.exp ((n + r : ℕ) : ℝ) *
          Real.exp (-(c + 1) * ((n + r : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hshift
  filter_upwards [eventually_ge_atTop (n₀ + r)] with N hN
  have heq : N - r + r = N := by omega
  rw [← heq]
  exact hn₀ (N - r) (by omega)

/-- The exact unnormalized orthonormal-frame slab tails used in Subag's
Lemma 20, from Chen's pressure convergence and the explicit Lemma 22 input. -/
theorem orthonormalSlabPartitionLowerTails_of_chen_and_lemma22
    (hChen : SourceLiteratureParisi.Chen2013FiniteParisi)
    (μ : FiniteMixture) (β : ℝ) (htail : PressureLowerTails μ β)
    (r : ℕ) (η t c : ℝ) (hη : 0 < η) (ht : 0 < t) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ e : Fin r → Vector N, Orthonormal ℝ e →
      (disorderLaw N μ.maxDegree).real
        (fixedSlabPartitionLowerTailEvent μ β η t
          (fun i => Real.sqrt (N : ℝ) • e i)) ≤ Real.exp (-c * (N : ℝ)) :=
  orthonormalSlabPartitionLowerTails_of_pressure_limit μ β _ htail
    (SourceLiteratureParisiTemperatureEven.finite_pressure_limit_all_real hChen μ β)
    r η t c hη ht hc

/-- The residual replicated limit needs Lemma 22 only for the physical
residual mixtures, at the original fixed inverse temperature. -/
theorem residualReplicatedLimit_of_chen_and_lemma22
    (hChen : SourceLiteratureParisi.Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (htail : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      PressureLowerTails (physicalResidualMixture μ q hq) β) :
    ResidualReplicatedLimit D := by
  apply LiteratureSubagResidualReplicatedLimit.residualReplicatedLimit_of_orthonormalSlabPartitionLowerTails D
  intro q hq
  exact orthonormalSlabPartitionLowerTails_of_chen_and_lemma22 hChen _ β (htail q hq)

/-- The lower-band interface follows from Chen and precisely the residual
instances of Lemma 22, with the original quantifiers unchanged. -/
theorem expectedBandLowerApproximation_of_chen_and_lemma22
    (hChen : SourceLiteratureParisi.Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (htail : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      PressureLowerTails (physicalResidualMixture μ q hq) β) :
    LiteratureSubagTheorem5Proof.ExpectedBandLowerApproximation D :=
  LiteratureSubagThickLatitudeLower.expectedBandLowerApproximation_of_residualLimit D
    (residualReplicatedLimit_of_chen_and_lemma22 hChen D htail)


/-! The literal manuscript endpoints, with the lower-band input discharged. -/
open SourceMainTheoremsChenLower
open SourceLiteratureParisi SourceLiteratureGroundState
open LiteratureSubagTheorem5Proof LiteratureSubagRemark25Final
universe u v

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalEffectiveField SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceFiniteMixtureMainLiteral


/-- `finiteMixture_main_condensed_and_initial_literal`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem finiteMixture_main_condensed_and_initial_literal_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact finiteMixture_main_condensed_and_initial_literal_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage


/-- `finiteMixture_all_initial_spherical`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem finiteMixture_all_initial_spherical_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferPureAllInitial SourceInitialQuantitativeInput
open SourceInitialPolynomialMenu SourceInitialEntropyInformation
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteraturePhysicalNormQ LiteratureSubagTAP LiteratureSubagReplicaExclusion
open LiteratureSubagProposition24 PureReplicaMeanEnergyAssembly PurePhysicalHighEnergyRelocation
open SphericalOverlapExponential SphericalOrthogonalHaar
open scoped Topology NNReal ENNReal
open SourcePureMainTheoremsLiterature


/-- `pure_corollary_a_all_initial`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem pure_corollary_a_all_initial_of_chen_and_lemma22
    (p : ℕ)
    (hp : 4 ≤ p)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      SphericalOrthogonalHaar.uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (ν : ∀ N, ι N → Measure (Vector N))
        [∀ N j, IsProbabilityMeasure (ν N j)],
        (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N) (exponentialGridHorizon γ N)) 1) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
        (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
        (ν : ∀ N, R N → ι N → Measure (Vector N)),
        (∀ N j, Measurable (fun r => ν N r j)) →
        ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
        (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => (ρ N).prod (SphericalFieldKernels.fieldLaw N μ))
          (fun N z => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N z.1) (exponentialGridHorizon γ N) z.2) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        ReductionEntropy.LittleLogInProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
        ReductionInformation.LittleLog
          (fun N => endpointMutualInformation
            (SphericalFieldKernels.fieldLaw N μ) (κ N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) := by
  exact pure_corollary_a_all_initial_of_chen_and_lower
    (p := p) (hp := hp) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature


/-- `convex_corollary_b`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem convex_corollary_b_of_chen_and_lemma22
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact convex_corollary_b_of_chen_and_lower
    (μ := μ) (hd := hd) (hβ := hβ) (hξ := hξ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature


/-- `degree_window_corollary_b`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem degree_window_corollary_b_of_chen_and_lemma22
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact degree_window_corollary_b_of_chen_and_lower
    (μ := μ) (hd := hd) (hwindow := hwindow) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set SphericalModel SourceMainClassesLiterature
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceMainClassesDegreeWindow


/-- `support_four_through_eleven_corollary_b`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem support_four_through_eleven_corollary_b_of_chen_and_lemma22
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact support_four_through_eleven_corollary_b_of_chen_and_lower
    (μ := μ) (hsupport := hsupport) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature


/-- `nonconvex_corollary_d`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem nonconvex_corollary_d_of_chen_and_lemma22
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    MainCondensedAndInitialLiteral
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := by
  exact nonconvex_corollary_d_of_chen_and_lower
    (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureDirectingFullToScore PureCapturePhysicalFullToScore
open PureCaptureOverlapScoreCoordinates PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalCoarseDiniAssembly DirectingPhysical
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceSphericalSelfAveraging
open scoped Topology BigOperators ENNReal
open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalInfiniteAsymptoticLift
open SourceDirectingFamilies

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]


/-- `directing_norm`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem directing_norm_of_chen_and_lemma22
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (d : Measure Ω)
    [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 = Q} = 1 := by
  exact directing_norm_of_chen_and_lower
    (hChen := hChen) (h := h) (d := d) (hL := hL) (F := F)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalMarkedWindows TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SphericalGaussianJet SphericalForm SourceReductionClosedBandGraph
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open scoped Topology NNReal
open SourcePureAmplitudeScaling


/-- `pureBranchFixedWindowCapture`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem pureBranchFixedWindowCapture_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    PureBranchFixedWindowCapture μ β x Q := by
  exact pureBranchFixedWindowCapture_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal
open SourceMixedCaptureCommonWitness


/-- `mixed_original_fixed_window_capture`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem mixed_original_fixed_window_capture_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ,
        Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ))
          atTop (𝓝 (markE μ β x Q)) ∧
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M (Icc L R))
            atTop < ⊤) ∧
        ∀ b : ℝ, 0 < b → b ≤ b₀ →
          Tendsto (fun M : ℝ => limsup (fun n =>
            ∫ J, originalBandComplementMass μ Q (m n) M b β
              (Icc L R) J ∂disorderLaw (n+2) μ.maxDegree) atTop)
            atTop (𝓝 0) := by
  exact mixed_original_fixed_window_capture_of_chen_and_lower
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SourceMixedCountCapturePackage


/-- `mixed_count_capture_package`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem mixed_count_capture_package_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ C cut η ε L R b₀ : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss
        ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        CountCapturePackage μ β x Q L R b₀ d.center ∧
        ∀ t : ℝ, 0 < t → MixedSharpAtWindow μ β x Q C cut η ε L R d.center t := by
  exact mixed_count_capture_package_of_chen_and_lower
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage


/-- `pure_normalized_count_capture_package`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem pure_normalized_count_capture_package_of_chen_and_lemma22
    (p : ℕ)
    (hp : 2 ≤ p)
    (a : ℝ)
    (ha : 0 < a)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ L R b₀ C cut η ε δ : ℝ, ∃ m : ℕ → ℝ,
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < δ ∧
      0 < cut ∧ cut ≤ 1 ∧ 0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      CountCapturePackage μ β x Q L R b₀ m ∧
      (∀ᶠ n : ℕ in atTop, ExpectedTailCentering.tail
        (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ))) (m n) = 1) ∧
      ∀ t : ℝ, 0 < t → PureSharpAtWindow μ β x Q C cut η ε δ m t ∧
        PureWindowIdentification μ β x Q C η ε δ L R m t := by
  exact pure_normalized_count_capture_package_of_chen_and_lower
    (p := p) (hp := hp) (a := a) (ha := ha) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage


/-- `finiteMixture_count_capture_package`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem finiteMixture_count_capture_package_of_chen_and_lemma22
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ L R b₀ : ℝ, sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧ 0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ, CountCapturePackage μ β x Q L R b₀ m := by
  exact finiteMixture_count_capture_package_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open LiteratureSubagPhysicalDefinitions LiteratureSubagContact


/-- `source_normalized_replica_exclusion`, with Chen and the explicit Lemma 22 hypothesis. -/
theorem source_normalized_replica_exclusion_of_chen_and_lemma22
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hn : ¬ MultiSamplable μ β q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  exact source_normalized_replica_exclusion_of_chen_and_lower
    (D := D) (hβ := hβ) (hq := hq) (hn := hn) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_chen_and_lemma22 hChen _
      (fun _ _ => hLemma22 _ _))

end

section

open CSPerturbative SourceFiniteMixtureMainLiteral SourceMainClassesLiterature

/-- `cor:main-classes(c)`, with the common cutoff chosen before the
perturbation and no remaining lower-band implication. -/
theorem perturbative_corollary_c_of_chen_and_lemma22 (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β)
    (hChen : Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          MainCondensedAndInitialLiteral μ β := by
  obtain ⟨ε₀, hε₀, hresult⟩ :=
    SourceMainTheoremsChenLower.perturbative_corollary_c_of_chen_and_lower
      d P hd hdEven hdP hβ hChen
  refine ⟨ε₀, hε₀, ?_⟩
  intro b hb ε hε hsmall
  dsimp only
  exact hresult b hb ε hε hsmall
    (expectedBandLowerApproximation_of_chen_and_lemma22 hChen _ (fun _ _ => hLemma22 _ _))

end

section

open CrisantiSommers CSParisiMeasure LiteratureSubagContact
open SourceGroundProfileUniqueness SourceGeneralContactTheorem
open SourceMainTheoremsReducedFinal

/-- `thm:th-contact(1)`, with Chen and Lemma 22 as its literature inputs. -/
theorem contact_iff_multiSamplable_of_chen_and_lemma22 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β)
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    MultiSamplable μ β q ↔
      CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0 :=
  LiteratureSubagTheorem10Proof2.Endpoints.contact_iff_multiSamplable hChen D hβ
    (expectedBandLowerApproximation_of_chen_and_lemma22 hChen D (fun _ _ => hLemma22 _ _)) hq

/-- `thm:th-contact(2)` already needs only Chen. -/
theorem contact_ground_profile_unique_of_chen_and_lemma22 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0) :
    let u := groundTrial (canonicalMinimizer μ β) hβ hq (le_refl (0 : ℝ))
    (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
    D.ground q = radiusFunctional μ u ∧
    (∀ v : RadiusGroundProfile q,
      (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
      ∀ r ∈ Icc (0 : ℝ) q,
        radiusProfile v r = β * xHat (canonicalMinimizer μ β).law r) :=
  LiteratureSubagTheorem10Proof2.Endpoints.contact_ground_profile_unique hChen D hβ hq hV

/-- `prop:th-structure`, with the full physical lower approximation discharged. -/
theorem strict_oneStep_structure_of_chen_and_lemma22 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : SphericalTAPCertificate.Certificate μ β x Q)
    (D : ThermodynamicData μ β)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β) :
    StrictOneStepConclusions h D :=
  LiteratureSubagTheorem10Proof2.Endpoints.strict_oneStep_structure hChen h D
    (expectedBandLowerApproximation_of_chen_and_lemma22 hChen D (fun _ _ => hLemma22 _ _))

/-- `thm:th-subag(1)`, including zero overlap. -/
theorem source_subag_tap_of_chen_and_lemma22 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β)
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    SourceSubagReplicaCriterion.sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = SourceSubagReplicaCriterion.sourceTAPValue D q ↔
        MultiSamplable μ β q) :=
  LiteratureSubagTheorem10Proof2.Endpoints.source_subag_tap hChen D hβ
    (expectedBandLowerApproximation_of_chen_and_lemma22 hChen D (fun _ _ => hLemma22 _ _)) hq

/-- `thm:th-subag(2)`, including zero overlap. -/
theorem source_replica_criterion_of_chen_and_lemma22 (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β)
    (hLemma22 : ∀ μ : FiniteMixture, ∀ β : ℝ, PressureLowerTails μ β)
    (hq : q ∈ Ico (0 : ℝ) 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ)
        atTop = 0) ↔ MultiSamplable μ β q :=
  LiteratureSubagTheorem10Proof2.Endpoints.source_replica_criterion hChen hβ
    (expectedBandLowerApproximation_of_chen_and_lemma22 hChen _ (fun _ _ => hLemma22 _ _)) hq

end

section

open CrisantiSommers CSTAPGroundTrialQuadratic

/-- `thm:th-contact(3)`, quantitative gap; this part needs Chen alone. -/
theorem tapValue_le_pressure_sub_gap_of_chen_and_lemma22
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β)
    (D : ThermodynamicData μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q ≤ D.pressure -
      (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        (8*β^3*curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) :=
  SourceMainTheoremsReducedFinal.tapValue_le_pressure_sub_gap_of_chen hChen hβ D hq hV

/-- `thm:th-contact(3)`, strict gap; this part needs Chen alone. -/
theorem strict_tap_gap_of_chen_and_lemma22
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β)
    (D : ThermodynamicData μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q < D.pressure :=
  SourceMainTheoremsReducedFinal.strict_tap_gap_of_chen hChen hβ D hq hV

/-- `thm:th-contact(3)`, compact uniform gap; this part needs Chen alone. -/
theorem compact_uniform_tap_gap_of_chen_and_lemma22
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (D : ThermodynamicData μ β) {K : Set ℝ}
    (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ K, tapValue D q ≤ D.pressure-δ :=
  SourceMainTheoremsReducedFinal.compact_uniform_tap_gap_of_chen hChen hβ D hK hKsub hKzero

end

section

open CrisantiSommers CSParisiMeasure CSTAPGroundTrialQuadratic
open scoped ENNReal

/-- The residual minimizer clause of `thm:th-contact(2)` is deterministic. -/
theorem contact_residual_canonical_of_chen_and_lemma22
    {μ : FiniteMixture} {β q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0) :
    (canonicalMinimizer (physicalResidualMixture μ q hq) β).law =
      (canonicalMinimizer μ β).law.map (fun r => max 0 ((r-q)/(1-q))) :=
  SourceMainTheoremsReducedFinal.contact_residual_canonical_of_chen hq hV

/-- The literal coefficient `M_q` in `thm:th-contact(3)`. -/
theorem curvature_eq_source_of_chen_and_lemma22 (β : ℝ) (ζ : Measure ℝ) (q : ℝ) :
    curvature β ζ q = 1/β^3 * ∫ v in (0 : ℝ)..q, (q-v)^2/(xHat ζ v)^3 :=
  SourceGeneralContactTheorem.curvature_eq_source β ζ q

/-- Positivity and the printed upper bound for `M_q` require no literature input. -/
theorem contact_curvature_bounds_of_chen_and_lemma22
    (μ : FiniteMixture) {β q : ℝ} (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < curvature β (canonicalMinimizer μ β).law q ∧
      curvature β (canonicalMinimizer μ β).law q ≤
        q^3/(3*β^3*xHat (canonicalMinimizer μ β).law q^3) :=
  ⟨SourceGeneralContactTheorem.ground_trial_curvature_pos _ hβ hq,
    SourceGeneralContactTheorem.ground_trial_curvature_le _ hβ hq⟩

/-- The literal positive compact infimum in `thm:th-contact(3)`. -/
theorem compact_inf_contact_gap_of_chen_and_lemma22
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (canonicalMinimizer μ β).law q ≠ 0) :
    0 < ⨅ q : K, ENNReal.ofReal
      ((CSStructure.potential μ β (canonicalMinimizer μ β).law q)^2 /
        curvature β (canonicalMinimizer μ β).law q) :=
  SourceGeneralContactTheorem.compact_inf_contact_gap μ hβ hK hKsub hKzero

end

end SlowEquilibration.LiteratureSubagSlabTails
