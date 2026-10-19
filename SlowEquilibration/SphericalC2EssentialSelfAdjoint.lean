-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGroundStateUnitary
public import SlowEquilibration.UnitaryBoundedPerturbationCore
public import SlowEquilibration.SphericalEssentialSelfAdjoint

/-! Essential self-adjointness on actual C² spherical tests, derived from
the genuine smooth zero-temperature core and the bounded ground-state transform. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalForm
open MeasureTheory Set SphericalModel
open scoped InnerProductSpace ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000

theorem groundStateWeight_zero (N : ℕ) (H : Vector N → ℝ) (x : Vector N) :
    groundStateWeight N 0 H x = 1 := by
  let _ := sphereLaw_probability N
  simp [groundStateWeight,partition]

theorem groundStateUnitary_zero_continuous {N : ℕ} (hN : 1 ≤ N)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : Continuous f) :
    groundStateUnitary hN 0 H hH (gibbsToL2 hN 0 H hH f hf) = groundSphereToL2 hN f hf := by
  apply Lp.ext
  have hac := PositiveDensityL2.reverse_absolutelyContinuous (sphereLaw N) (gibbsLaw N 0 H)
    (groundStateWeight N 0 H) (groundStateWeight_continuous 0 hH).measurable
    (groundStateWeight_pos hN 0 hH) (gibbsLaw_eq_groundStateDensity hN 0 hH)
  filter_upwards [groundStateUnitary_coe hN 0 H hH (gibbsToL2 hN 0 H hH f hf),
    (gibbsToL2_coe hN 0 H hH f hf).filter_mono hac.ae_le,groundSphereToL2_coe hN f hf]
    with x hx hy hz
  rw [hx,hy,hz,groundStateWeight_zero,one_mul]

theorem groundSphereToL2_add {N : ℕ} (hN : 1 ≤ N) (f g : Vector N → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    groundSphereToL2 hN (f+g) (hf.add hg) =
      groundSphereToL2 hN f hf + groundSphereToL2 hN g hg := rfl

theorem groundSphereToL2_neg {N : ℕ} (hN : 1 ≤ N) (f : Vector N → ℝ)
    (hf : Continuous f) :
    groundSphereToL2 hN (-f) hf.neg = -groundSphereToL2 hN f hf := rfl

theorem groundStatePotentialOperator_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (f : Vector N → ℝ) (hf : Continuous f) :
    groundStatePotentialOperator hN β H hH (groundSphereToL2 hN f hf) =
      groundSphereToL2 hN (fun x => groundStatePotential N β H x*f x)
        ((groundStatePotential_continuous β hH).mul hf) := by
  apply Lp.ext
  filter_upwards [groundStatePotentialLinear_coe hN β H hH (groundSphereToL2 hN f hf),
    groundSphereToL2_coe hN f hf,
    groundSphereToL2_coe hN (fun x => groundStatePotential N β H x*f x)
      ((groundStatePotential_continuous β hH).mul hf)] with x hx hf hg
  change groundStatePotentialLinear hN β H hH (groundSphereToL2 hN f _) x = _
  rw [hx,hf,hg]

def c2Functions (N : ℕ) : Submodule ℝ (Vector N → ℝ) where
  carrier := {f | ContDiff ℝ 2 f}
  zero_mem' := by change ContDiff ℝ 2 (fun _ : Vector N => (0 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ 2 f from hf).add (show ContDiff ℝ 2 g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ 2 f from hf).const_smul c

theorem c2Functions_contDiff {N : ℕ} (f : c2Functions N) :
    ContDiff ℝ 2 (f : Vector N → ℝ) := f.property

def c2ValueLinear {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : c2Functions N →ₗ[ℝ] Lp ℝ 2 (gibbsLaw N β H) where
  toFun f := gibbsToL2 hN β H hH f (c2Functions_contDiff f).continuous
  map_add' f g := gibbsToL2_add hN β H hH f g (c2Functions_contDiff f).continuous (c2Functions_contDiff g).continuous
  map_smul' c f := gibbsToL2_smul hN β H hH f (c2Functions_contDiff f).continuous c

private theorem hasCore_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E) (hA : A.IsClosed) {C D : Submodule ℝ E}
    (hC : A.HasCore C) (hCD : C ≤ D) (hD : D ≤ A.domain) : A.HasCore D := by
  have hc : (A.domRestrict D).IsClosable := hA.isClosable.leIsClosable LinearPMap.domRestrict_le
  refine ⟨hD,le_antisymm ?_ ?_⟩
  · have hh := hA.isClosable.closure_mono (show A.domRestrict D ≤ A from LinearPMap.domRestrict_le)
    have he : A.closure=A := LinearPMap.eq_of_eq_graph
      (hA.isClosable.graph_closure_eq_closure_graph.symm.trans hA.submodule_topologicalClosure_eq)
    rwa [he] at hh
  · conv_lhs => rw [← hC.closure_eq]
    apply hc.closure_mono
    exact ⟨inf_le_inf hCD le_rfl,fun x y hxy => LinearPMap.domRestrict_apply hxy⟩

/-- C² functions are an actual operator core for every C² Gibbs potential. -/
private theorem sphericalGenerator_C2_hasCore_from_finite {N : ℕ}
    (μ₀ : FiniteMixture) (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    (sphericalGenerator hN β H hH.continuous).HasCore
      (LinearMap.range (c2ValueLinear hN β H hH.continuous)) := by
  let H₀ := fieldOfMixture μ₀ (0 : Disorder N μ₀.maxDegree)
  have hH₀ : ContDiff ℝ ∞ H₀ := (fieldOfMixture_contDiff μ₀ 0).of_le (by simp)
  let E := Lp ℝ 2 (gibbsLaw N 0 H₀)
  let F := Lp ℝ 2 (gibbsLaw N β H)
  let A := sphericalGenerator hN 0 H₀ hH₀.continuous
  let B := sphericalGenerator hN β H hH.continuous
  let S := groundStateUnitary hN 0 H₀ hH₀.continuous
  let T := groundStateUnitary hN β H hH.continuous
  let U : E ≃ₗᵢ[ℝ] F := S.trans T.symm
  let W := groundStatePotentialOperator hN β H hH
  let V : F →L[ℝ] F := T.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (W.comp T.toContinuousLinearEquiv.toContinuousLinearMap)
  let C := LinearMap.range (smoothValueLinear hN 0 H₀ hH₀.continuous)
  have hC : A.HasCore C := mixed_sphericalGenerator_hasCore hN μ₀ 0 0
  have hV : V.IsSymmetric := by
    intro u v
    have hw := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (groundStatePotentialOperator_selfAdjoint hN β H hH)) (T u) (T v)
    change inner ℝ (W (T u)) (T v)=inner ℝ (T u) (W (T v)) at hw
    calc
      inner ℝ (V u) v = inner ℝ (T (V u)) (T v) := (T.inner_map_map _ _).symm
      _ = inner ℝ (T u) (T (V v)) := by
        change inner ℝ (T (T.symm (W (T u)))) (T v) =
          inner ℝ (T u) (T (T.symm (W (T v))))
        simpa only [T.apply_symm_apply] using hw
      _ = inner ℝ u (V v) := T.inner_map_map _ _
  have hu (q : smoothCore N) : U (smoothValueLinear hN 0 H₀ hH₀.continuous q) =
      T.symm (groundSphereToL2 hN q (smoothCore_contDiff q).continuous) :=
    congrArg T.symm (groundStateUnitary_zero_continuous hN H₀ hH₀.continuous q
      (smoothCore_contDiff q).continuous)
  have hdom : ∀ x : C,U x∈B.domain := by
    rintro ⟨x,q,rfl⟩
    rw [hu]
    exact (sphericalGenerator_groundState_C2 hN β H hH q
      ((smoothCore_contDiff q).of_le (by simp))).choose
  have hact : ∀ x : C,B ⟨U x,hdom x⟩ = U (A ⟨x,hC.le_domain x.property⟩)+V (U x) := by
    rintro ⟨x,q,rfl⟩
    have hq : ContDiff ℝ 2 (q : Vector N → ℝ) := (smoothCore_contDiff q).of_le (by simp)
    obtain ⟨hd,hb⟩ := sphericalGenerator_groundState_C2 hN β H hH q hq
    have hleft : T (B ⟨U (smoothValueLinear hN 0 H₀ hH₀.continuous q),
      hdom ⟨smoothValueLinear hN 0 H₀ hH₀.continuous q,⟨q,rfl⟩⟩⟩) =
        groundSphereToL2 hN (fun x => -rotationLaplacian N q x + groundStatePotential N β H x*q.val x)
          ((rotationLaplacian_continuous hq).neg.add
            ((groundStatePotential_continuous β hH).mul hq.continuous)) := by
      convert hb using 1
      congr 2
      exact Subtype.ext (hu q)
    obtain ⟨ha,hAa⟩ := sphericalGenerator_C2 hN 0 H₀ (hH₀.of_le (by simp)) q hq
    have hzero : rotationGenerator N 0 H₀ q=rotationLaplacian N q := by
      funext x
      simp only [rotationGenerator,zero_mul,add_zero]
    apply T.injective
    rw [map_add,hleft]
    have hU (z : E) : T (U z)=S z := T.apply_symm_apply _
    rw [hU]
    change _ = S (A ⟨smoothValueLinear hN 0 H₀ hH₀.continuous q,_⟩)+T (V (U _))
    erw [hAa]
    rw [map_neg,groundStateUnitary_zero_continuous]
    have hVU : T (V (U (smoothValueLinear hN 0 H₀ hH₀.continuous q))) =
        W (groundSphereToL2 hN q (smoothCore_contDiff q).continuous) := by
      change T (T.symm (W (T (U _))))=_
      rw [T.apply_symm_apply,hu,T.apply_symm_apply]
    rw [hVU,groundStatePotentialOperator_continuous]
    rw [← groundSphereToL2_neg,← groundSphereToL2_add]
    apply Lp.ext
    filter_upwards [groundSphereToL2_coe hN
      (fun x => -rotationLaplacian N q x + groundStatePotential N β H x*q.val x) _,
      groundSphereToL2_coe hN
        ((-rotationGenerator N 0 H₀ q)+(fun x => groundStatePotential N β H x*q.val x)) _]
      with x hx hy
    rw [hx,hy]
    simp only [Pi.add_apply,Pi.neg_apply,hzero]
  have hc := UnitaryBoundedPerturbation.hasCore_of_unitary_bounded_perturbation
    A B (sphericalGenerator_selfAdjoint hN 0 H₀ hH₀.continuous)
    (sphericalGenerator_selfAdjoint hN β H hH.continuous) U V hV C hC hdom hact
  apply hasCore_mono B (sphericalGenerator_selfAdjoint hN β H hH.continuous).isClosed hc
  · rintro x ⟨y,⟨q,rfl⟩,rfl⟩
    have hq : ContDiff ℝ 2 (q : Vector N → ℝ) := (smoothCore_contDiff q).of_le (by simp)
    have hdiv := hq.div (groundStateWeight_contDiff β hH)
      (fun x => (groundStateWeight_pos hN β hH.continuous x).ne')
    refine ⟨⟨fun x => q.val x/groundStateWeight N β H x,hdiv⟩,?_⟩
    change gibbsToL2 hN β H hH.continuous
      (fun x => q.val x/groundStateWeight N β H x) hdiv.continuous =
      U (smoothValueLinear hN 0 H₀ hH₀.continuous q)
    rw [hu]
    exact (groundStateUnitary_symm_continuous hN β H hH.continuous q hq.continuous).symm
  · rintro x ⟨f,rfl⟩
    exact (sphericalGenerator_C2 hN β H (hH.of_le (by norm_num)) f (c2Functions_contDiff f)).choose

theorem sphericalGenerator_C2_hasCore {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    (sphericalGenerator hN β H hH.continuous).HasCore
      (LinearMap.range (c2ValueLinear hN β H hH.continuous)) :=
  sphericalGenerator_C2_hasCore_from_finite (FiniteMixture.pure 2 (by omega) 1 (by norm_num)) hN β H hH

def sphericalC2DifferentialOperator {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    Lp ℝ 2 (gibbsLaw N β H) →ₗ.[ℝ] Lp ℝ 2 (gibbsLaw N β H) :=
  (sphericalGenerator hN β H hH.continuous).domRestrict
    (LinearMap.range (c2ValueLinear hN β H hH.continuous))

theorem sphericalC2DifferentialOperator_domain {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    (sphericalC2DifferentialOperator hN β H hH).domain =
      LinearMap.range (c2ValueLinear hN β H hH.continuous) :=
  inf_eq_left.mpr (sphericalGenerator_C2_hasCore hN β H hH).le_domain

theorem sphericalC2DifferentialOperator_apply {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (f : c2Functions N) :
    ∃ hf : c2ValueLinear hN β H hH.continuous f ∈
        (sphericalC2DifferentialOperator hN β H hH).domain,
      sphericalC2DifferentialOperator hN β H hH
        ⟨c2ValueLinear hN β H hH.continuous f,hf⟩ =
      -gibbsToL2 hN β H hH.continuous (rotationGenerator N β H f)
        (rotationGenerator_continuous β (hH.of_le (by norm_num)) (c2Functions_contDiff f)) := by
  obtain ⟨hf,hA⟩ := sphericalGenerator_C2 hN β H (hH.of_le (by norm_num)) f
    (c2Functions_contDiff f)
  refine ⟨⟨⟨f,rfl⟩,hf⟩,?_⟩
  exact hA

theorem sphericalC2DifferentialOperator_closure {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    (sphericalC2DifferentialOperator hN β H hH).closure =
      sphericalGenerator hN β H hH.continuous :=
  (sphericalGenerator_C2_hasCore hN β H hH).closure_eq

theorem sphericalC2DifferentialOperator_essentiallySelfAdjoint {N : ℕ}
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    IsSelfAdjoint (sphericalC2DifferentialOperator hN β H hH).closure := by
  rw [sphericalC2DifferentialOperator_closure]
  exact sphericalGenerator_selfAdjoint hN β H hH.continuous

end SlowEquilibration.SphericalForm
