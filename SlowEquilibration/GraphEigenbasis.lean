module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic

@[expose] public section

/-!
# The actual singular-system Hilbert basis of an energy graph

For an injective Hilbert inclusion `J` and an eigen Hilbert basis of
`J ∘ J*`, the normalized adjoint images form a genuine Hilbert basis of the
energy graph. This turns resolvent eigenvalues into exact form coefficients.
-/

namespace SlowEquilibration.GraphEigenbasis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators InnerProductSpace Topology

variable {I E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual normalized adjoint image of a resolvent eigenvector. -/
def graphVector (J : F →L[ℝ] E) (b : HilbertBasis I ℝ E) (μ : I → ℝ) (i : I) : F :=
  (Real.sqrt (μ i))⁻¹ • J.adjoint (b i)

theorem graphVector_inner (J : F →L[ℝ] E) (b : HilbertBasis I ℝ E) (μ : I → ℝ)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (i j : I) :
    inner ℝ (graphVector J b μ i) (graphVector J b μ j) =
      (Real.sqrt (μ i))⁻¹ * ((Real.sqrt (μ j))⁻¹ * (μ i * inner ℝ (b i) (b j))) := by
  unfold graphVector
  rw [real_inner_smul_left, real_inner_smul_right,
    J.adjoint_inner_right, he i, real_inner_smul_left]

theorem graphVector_orthonormal (J : F →L[ℝ] E) (b : HilbertBasis I ℝ E) (μ : I → ℝ)
    (hμ : ∀ i, 0 < μ i) (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) :
    Orthonormal ℝ (graphVector J b μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [graphVector_inner J b μ he, orthonormal_iff_ite.mp b.orthonormal i j]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one]
    have hs : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr (hμ i)).ne'
    have hsq : Real.sqrt (μ i) ^ 2 = μ i := Real.sq_sqrt (hμ i).le
    field_simp
    nlinarith only [hsq]
  · simp [hij]

theorem graphVector_coefficient (J : F →L[ℝ] E) (b : HilbertBasis I ℝ E) (μ : I → ℝ)
    (u : F) (i : I) :
    inner ℝ (graphVector J b μ i) u = (b.repr (J u) i) / Real.sqrt (μ i) := by
  rw [graphVector, real_inner_smul_left, J.adjoint_inner_left, HilbertBasis.repr_apply_apply]
  rw [div_eq_mul_inv, mul_comm]

/-- Injectivity of the actual graph inclusion proves completeness of the
normalized adjoint eigenvectors; no graph eigenbasis premise is assumed. -/
theorem graphVector_span_orthogonal_eq_bot (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i) :
    (Submodule.span ℝ (Set.range (graphVector J b μ)))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hi (i : I) : inner ℝ (graphVector J b μ i) u = 0 :=
    hu _ (Submodule.subset_span ⟨i, rfl⟩)
  have hzero : J u = 0 := by
    apply b.repr.injective
    apply lp.ext
    funext i
    have hr0 : b.repr (0 : E) i = 0 := by
      rw [HilbertBasis.repr_apply_apply, inner_zero_right]
    rw [hr0]
    have h := hi i
    rw [graphVector_coefficient] at h
    exact (div_eq_zero_iff.mp h).resolve_right (Real.sqrt_pos.mpr (hμ i)).ne'
  exact hJ (hzero.trans (map_zero J).symm)

/-- The genuine Hilbert basis of the actual energy graph induced by the
resolvent eigenbasis. -/
def graphBasis (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) : HilbertBasis I ℝ F :=
  HilbertBasis.mkOfOrthogonalEqBot (graphVector_orthonormal J b μ hμ he)
    (graphVector_span_orthogonal_eq_bot J hJ b μ hμ)

@[simp] theorem graphBasis_apply (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (i : I) :
    graphBasis J hJ b μ hμ he i = graphVector J b μ i := by
  simp only [graphBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem graphBasis_coefficient (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (u : F) (i : I) :
    (graphBasis J hJ b μ hμ he).repr u i = (b.repr (J u) i) / Real.sqrt (μ i) := by
  rw [HilbertBasis.repr_apply_apply, graphBasis_apply, graphVector_coefficient]

/-- Exact Parseval formula for the energy graph norm in actual resolvent
coordinates. The identity is proved from the constructed graph basis. -/
theorem graph_norm_hasSum (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (u : F) :
    HasSum (fun i => (b.repr (J u) i) ^ 2 / μ i) (‖u‖ ^ 2) := by
  have hs := (graphBasis J hJ b μ hμ he).hasSum_inner_mul_inner u u
  have hterm (i : I) :
      inner ℝ u (graphBasis J hJ b μ hμ he i) *
        inner ℝ (graphBasis J hJ b μ hμ he i) u = (b.repr (J u) i) ^ 2 / μ i := by
    have hc : inner ℝ (graphBasis J hJ b μ hμ he i) u =
        (b.repr (J u) i) / Real.sqrt (μ i) := by
      rw [graphBasis_apply]
      exact graphVector_coefficient J b μ u i
    have hcomm : inner ℝ u (graphBasis J hJ b μ hμ he i) =
        inner ℝ (graphBasis J hJ b μ hμ he i) u := real_inner_comm _ _
    rw [hcomm, hc]
    have hsq : Real.sqrt (μ i) ^ 2 = μ i := Real.sq_sqrt (hμ i).le
    rw [← pow_two, div_pow, hsq]
  simpa only [hterm, real_inner_self_eq_norm_sq] using hs

/-- Exact closed-form energy coefficients, obtained by subtracting actual
L² Parseval from actual energy-graph Parseval. -/
theorem graph_energy_hasSum (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (u : F) :
    HasSum (fun i => ((μ i)⁻¹ - 1) * (b.repr (J u) i) ^ 2) (‖u‖ ^ 2 - ‖J u‖ ^ 2) := by
  have hg := graph_norm_hasSum J hJ b μ hμ he u
  have hl := b.hasSum_inner_mul_inner (J u) (J u)
  have heq (i : I) : inner ℝ (J u) (b i) * inner ℝ (b i) (J u) = (b.repr (J u) i) ^ 2 := by
    have hcomm : inner ℝ (J u) (b i) = inner ℝ (b i) (J u) := real_inner_comm _ _
    have hc : inner ℝ (b i) (J u) = b.repr (J u) i := (b.repr_apply_apply (J u) i).symm
    rw [hcomm, hc, pow_two]
  simp only [heq, real_inner_self_eq_norm_sq] at hl
  have hd := hg.sub hl
  convert hd using 1
  funext i
  rw [div_eq_mul_inv]
  ring

/-- Membership in the actual energy graph range is characterized by the
actual inverse-resolvent weighted square coefficients. -/
theorem range_iff_summable_inverse (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (f : E) :
    (∃ u : F, J u = f) ↔ Summable (fun i => (b.repr f i) ^ 2 / μ i) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (graph_norm_hasSum J hJ b μ hμ he u).summable
  · intro hs
    let c : I → ℝ := fun i => (b.repr f i) / Real.sqrt (μ i)
    have hc : Memℓp c 2 := by
      rw [memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)]
      have hterm (i : I) : ‖c i‖ ^ (2 : ENNReal).toReal = (b.repr f i) ^ 2 / μ i := by
        norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
        dsimp [c]
        rw [sq_abs, div_pow, Real.sq_sqrt (hμ i).le]
      exact hs.congr (fun i => (hterm i).symm)
    let a : lp (fun _ : I => ℝ) 2 := ⟨c, hc⟩
    let u : F := (graphBasis J hJ b μ hμ he).repr.symm a
    have hu (i : I) : (graphBasis J hJ b μ hμ he).repr u i = c i := by
      dsimp [u]
      rw [LinearIsometryEquiv.apply_symm_apply]
    refine ⟨u, ?_⟩
    apply b.repr.injective
    apply lp.ext
    funext i
    have hcoef := graphBasis_coefficient J hJ b μ hμ he u i
    rw [hu i] at hcoef
    dsimp [c] at hcoef
    exact (div_left_inj' (Real.sqrt_pos.mpr (hμ i)).ne').mp hcoef.symm

/-- The form domain is characterized by the actual generator eigenvalue
weights `μ⁻¹−1`, using the actual L² Parseval theorem. -/
theorem range_iff_summable_generator (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (b : HilbertBasis I ℝ E) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : ∀ i, J (J.adjoint (b i)) = μ i • b i) (f : E) :
    (∃ u : F, J u = f) ↔ Summable (fun i => ((μ i)⁻¹ - 1) * (b.repr f i) ^ 2) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (graph_energy_hasSum J hJ b μ hμ he u).summable
  · intro hs
    apply (range_iff_summable_inverse J hJ b μ hμ he f).mpr
    have hl := b.hasSum_inner_mul_inner f f
    have hterm (i : I) : inner ℝ f (b i) * inner ℝ (b i) f = (b.repr f i) ^ 2 := by
      have hcomm : inner ℝ f (b i) = inner ℝ (b i) f := real_inner_comm _ _
      have hc : inner ℝ (b i) f = b.repr f i := (b.repr_apply_apply f i).symm
      rw [hcomm, hc, pow_two]
    simp only [hterm] at hl
    have hsum := hs.add hl.summable
    convert hsum using 1
    funext i
    rw [div_eq_mul_inv]
    ring

end
end SlowEquilibration.GraphEigenbasis
