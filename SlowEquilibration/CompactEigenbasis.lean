-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
-- lean/OAI/Analysis/CoulombIonization/FormDomain/CompactEigenbasis.lean.
-- Modifications: real Hilbert spaces; actual positive contraction bounds;
-- independent operator construction; Lean 4.35 public modules.
module

public import Mathlib

@[expose] public section

namespace SlowEquilibration.CompactEigenbasis

open MeasureTheory Filter Module Set Metric
open scoped Topology BigOperators InnerProductSpace
noncomputable section

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def compactEigenspaceIndex (T : H →L[ℝ] H) (μ : ℝ) : Set (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℝ (Module.End.eigenspace T.toLinearMap μ)).choose

def compactEigenspaceBasis (T : H →L[ℝ] H) (μ : ℝ) :
    HilbertBasis (compactEigenspaceIndex T μ) ℝ (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℝ (Module.End.eigenspace T.toLinearMap μ)).choose_spec.choose

abbrev CompactSpectralIndex (T : H →L[ℝ] H) := Σ μ : ℝ, compactEigenspaceIndex T μ

def compactSpectralVector (T : H →L[ℝ] H) (i : CompactSpectralIndex T) : H :=
  compactEigenspaceBasis T i.1 i.2

lemma compactSpectralVector_eigen (T : H →L[ℝ] H) (i : CompactSpectralIndex T) :
    T (compactSpectralVector T i) = i.1 • compactSpectralVector T i :=
  Module.End.mem_eigenspace_iff.mp (compactEigenspaceBasis T i.1 i.2).property

lemma compactSpectralVector_orthonormal (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric) :
    Orthonormal ℝ (compactSpectralVector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (compactEigenspaceBasis T μ).orthonormal)

lemma compactSpectralVector_orthogonal_eq_bot (T : H →L[ℝ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    (Submodule.span ℝ (Set.range (compactSpectralVector T)))ᗮ = ⊥ := by
  let S := Submodule.span ℝ (Set.range (compactSpectralVector T))
  have hs : (⨆ μ, Module.End.eigenspace T.toLinearMap μ) ≤ S.topologicalClosure := by
    apply iSup_le
    intro μ y hy
    let v : Module.End.eigenspace T.toLinearMap μ := ⟨y,hy⟩
    have hh := ((compactEigenspaceBasis T μ).hasSum_repr v).mapL
      (Module.End.eigenspace T.toLinearMap μ).subtypeL
    apply mem_closure_of_tendsto hh
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    change ((compactEigenspaceBasis T μ).repr v i) • (compactSpectralVector T ⟨μ,i⟩) ∈ S
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
  apply le_antisymm _ bot_le
  rw [← S.orthogonal_closure]
  exact (Submodule.orthogonal_le hs).trans
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs).le

def compactSpectralBasis (T : H →L[ℝ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    HilbertBasis (CompactSpectralIndex T) ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot (compactSpectralVector_orthonormal T hTs)
    (compactSpectralVector_orthogonal_eq_bot T hTc hTs)

lemma compactSpectralBasis_apply (T : H →L[ℝ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) : compactSpectralBasis T hTc hTs i = compactSpectralVector T i := by
  rw [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma compactSpectralBasis_eigen (T : H →L[ℝ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) :
    T (compactSpectralBasis T hTc hTs i) = i.1 • compactSpectralBasis T hTc hTs i := by
  simp only [compactSpectralBasis_apply,compactSpectralVector_eigen]


lemma orthonormal_countable {H : Type u} {ι : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [TopologicalSpace.SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2 : ℝ)) (Metric.ball (v j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℝ),hv.norm_eq_one,hv.norm_eq_one,hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.nonempty_ball.mpr (by norm_num))


/-- The genuine eigen-Hilbert basis has a countable index on every separable
real Hilbert space. Countability is proved from disjoint metric balls. -/
theorem compactSpectralIndex_countable [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℝ] H) (hs : T.toLinearMap.IsSymmetric) : Countable (CompactSpectralIndex T) :=
  orthonormal_countable (compactSpectralVector_orthonormal T hs)

omit [CompleteSpace H] in
/-- Every actual eigenvector of a strictly positive contraction has an
eigenvalue in `(0,1]`. -/
theorem eigenvalue_bounds (T : H →L[ℝ] H)
    (hp : ∀ f : H, f ≠ 0 → 0 < inner ℝ (T f) f) (hnorm : ‖T‖ ≤ 1)
    (μ : ℝ) (f : H) (hf : f ≠ 0) (he : T f = μ • f) : 0 < μ ∧ μ ≤ 1 := by
  have hpos := hp f hf
  rw [he, inner_smul_left_eq_smul, real_inner_self_eq_norm_sq, smul_eq_mul] at hpos
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hm : 0 < μ := (mul_pos_iff_of_pos_right (sq_pos_of_pos hn)).mp hpos
  refine ⟨hm, ?_⟩
  have h := T.le_opNorm f
  have hb := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hm] at h
  nlinarith

theorem compactSpectralBasis_eigenvalue_bounds (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric)
    (hp : ∀ f : H, f ≠ 0 → 0 < inner ℝ (T f) f) (hnorm : ‖T‖ ≤ 1)
    (i : CompactSpectralIndex T) : 0 < i.1 ∧ i.1 ≤ 1 := by
  apply eigenvalue_bounds T hp hnorm i.1 (compactSpectralBasis T hc hs i) _
    (compactSpectralBasis_eigen T hc hs i)
  intro hz
  have hn := (compactSpectralBasis T hc hs).orthonormal.norm_eq_one i
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- The compactness theorem gives finite multiplicity of every nonzero
actual eigenvalue. -/
theorem eigenspace_finite (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (μ : ℝ) (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ

/-- The actual transformed generator eigenvalue. -/
def generatorEigenvalue (T : H →L[ℝ] H) (i : CompactSpectralIndex T) : ℝ := i.1⁻¹-1

theorem generatorEigenvalue_nonneg (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric)
    (hp : ∀ f : H, f ≠ 0 → 0 < inner ℝ (T f) f) (hnorm : ‖T‖ ≤ 1)
    (i : CompactSpectralIndex T) : 0 ≤ generatorEigenvalue T i := by
  obtain ⟨hm, hmu⟩ := compactSpectralBasis_eigenvalue_bounds T hc hs hp hnorm i
  have hi : 1 ≤ i.1⁻¹ := (one_le_inv₀ hm).mpr hmu
  exact sub_nonneg.mpr hi

/-- Parseval's identity for the actual eigen-Hilbert basis. -/
theorem compactSpectralBasis_hasSum_sq_inner (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) (x : H) :
    HasSum (fun i => (inner ℝ (compactSpectralBasis T hc hs i) x)^2) (‖x‖^2) := by
  let b := compactSpectralBasis T hc hs
  have h := lp.hasSum_norm (by norm_num : 0 < (2:ENNReal).toReal) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs] using h

/-- The true compact operator is represented by the convergent spectral
series in its genuine eigen-Hilbert basis. -/
theorem compactSpectralBasis_hasSum_operator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) (x : H) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1 * inner ℝ (compactSpectralBasis T hc hs i) x) • compactSpectralBasis T hc hs i)
      (T x) := by
  have h := ((compactSpectralBasis T hc hs).hasSum_repr x).mapL T
  simpa only [map_smul, HilbertBasis.repr_apply_apply, compactSpectralBasis_eigen,
    smul_smul, mul_comm] using h

omit [CompleteSpace H] in
/-- Actual compactness forces only finitely many members of any orthonormal
eigenfamily to have eigenvalue at least a fixed positive scale. The proof
uses a finite metric cover of the image of the true unit ball. -/
theorem eigenvalue_superlevel_finite {ι : Type v} (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (e : ι → H) (μ : ι → ℝ)
    (ho : Orthonormal ℝ e) (he : ∀ i, T (e i) = μ i • e i)
    {c : ℝ} (hc0 : 0 < c) : {i | c ≤ μ i}.Finite := by
  classical
  have hcomp := hc.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hcomp.totallyBounded
    (c/2) (half_pos hc0)
  let S := {i | c ≤ μ i}
  have hnear (i : S) : ∃ a : t, dist (T (e i.val)) a < c/2 := by
    have hx : T (e i.val) ∈ closure (T '' closedBall 0 1) :=
      subset_closure ⟨e i.val, by simpa using (ho.norm_eq_one i.val).le, rfl⟩
    have hxcover := hcover hx
    simp only [mem_iUnion, mem_ball] at hxcover
    obtain ⟨a, ha, hai⟩ := hxcover
    exact ⟨⟨a, ha⟩, hai⟩
  choose f hf using hnear
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hinner : inner ℝ (e i.val) (T (e i.val)-T (e j.val)) = μ i.val := by
      rw [he i.val, he j.val, inner_sub_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, ho.norm_eq_one i.val, ho.inner_eq_zero hne]
      simp
    have hdist := real_inner_le_norm (e i.val) (T (e i.val)-T (e j.val))
    rw [ho.norm_eq_one i.val, one_mul, hinner, ← dist_eq_norm] at hdist
    have hd : dist (T (e i.val)) (T (e j.val)) < c := by
      have h1 := hf i
      have h2 := hf j
      rw [← hij] at h2
      have hh := dist_triangle (T (e i.val)) (f i : H) (T (e j.val))
      rw [dist_comm (f i : H) (T (e j.val))] at hh
      linarith
    exact (not_lt_of_ge (i.property.trans hdist)) hd
  let := ht.fintype
  let : Finite S := Finite.of_injective f hinj
  exact Set.toFinite S

/-- The actual eigenbasis weights have finite positive superlevel sets. -/
theorem compactSpectralBasis_superlevel_finite (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) {c : ℝ} (hc0 : 0 < c) :
    {i : CompactSpectralIndex T | c ≤ i.1}.Finite :=
  eigenvalue_superlevel_finite T hc (compactSpectralBasis T hc hs) (fun i => i.1)
    (compactSpectralBasis T hc hs).orthonormal (compactSpectralBasis_eigen T hc hs) hc0

/-- Positive actual eigenvalues tend to zero along the cofinite index filter,
before choosing any enumeration or ordering of the eigenbasis. -/
theorem compactSpectralBasis_weights_tendsto_zero_cofinite (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric)
    (hp : ∀ f : H, f ≠ 0 → 0 < inner ℝ (T f) f) (hnorm : ‖T‖ ≤ 1) :
    Tendsto (fun i : CompactSpectralIndex T => i.1) cofinite (𝓝 (0:ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnot := (compactSpectralBasis_superlevel_finite T hc hs hε).eventually_cofinite_notMem
  filter_upwards [hnot] with i hi
  obtain ⟨hpos, _⟩ := compactSpectralBasis_eigenvalue_bounds T hc hs hp hnorm i
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  exact lt_of_not_ge hi

end
end SlowEquilibration.CompactEigenbasis
