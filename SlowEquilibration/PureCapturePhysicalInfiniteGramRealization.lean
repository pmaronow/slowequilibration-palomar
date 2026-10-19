-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalInfiniteDSInput
public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-! Every genuine countably infinite physical overlap limit has a coherent
Hilbert-space Gram realization by unit vectors. The construction uses
Mathlib's positive-kernel RKHS theorem and does not assert the further
random iid directing-measure conclusion of Dovbysh--Sudakov. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalInfiniteGramRealization

open InnerProductSpace
open MeasureTheory ProbabilityTheory
open SlowEquilibration SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Embed a real scalar Gram kernel into operators on the real line. -/
def scalarKernel (c : Matrix ℕ ℕ ℝ) : Matrix ℕ ℕ (ℝ →L[ℝ] ℝ) :=
  fun i j => (c i j) • ContinuousLinearMap.id ℝ ℝ

/-- A positive scalar kernel stays positive as an operator-valued kernel. -/
theorem scalarKernel_posSemidef (c : Matrix ℕ ℕ ℝ) (hc : c.PosSemidef) :
    (scalarKernel c).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  constructor
  · ext i j
    have hsym : c j i = c i j := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
        congrFun (congrFun hc.isHermitian.eq i) j
    simp [Matrix.conjTranspose_apply, scalarKernel, hsym,
      ContinuousLinearMap.star_eq_adjoint]
  · intro vv
    rw [Finsupp.sum_comm]
    simpa [scalarKernel, RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]
      using hc.2 vv

/-- Every countably infinite positive real matrix is the Gram matrix
of vectors in one complete real Hilbert space. -/
theorem scalarKernel_gram (c : Matrix ℕ ℕ ℝ) (hc : c.PosSemidef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (v : ℕ → H),
      ∀ i j, inner ℝ (v i) (v j) = c i j := by
  let K := scalarKernel c
  let hK : K.PosSemidef := scalarKernel_posSemidef c hc
  haveI : Fact K.PosSemidef := ⟨hK⟩
  let H := RKHS.OfKernel K
  refine ⟨H, inferInstance, inferInstance, inferInstance,
    fun i => RKHS.kerFun H i 1, ?_⟩
  intro i j
  calc
    inner ℝ (RKHS.kerFun H i 1) (RKHS.kerFun H j 1) =
      inner ℝ (RKHS.kerFun H j 1) (RKHS.kerFun H i 1) := real_inner_comm ..
    _ = inner ℝ ((RKHS.kernel H i j) 1) 1 :=
      (RKHS.kernel_inner H i j 1 1).symm
    _ = c i j := by simp [H, K, scalarKernel, RCLike.inner_apply]

/-- Positivity of all finite initial principal matrices implies positivity
of the countably infinite matrix, since each finite-support test lies in
one initial segment. -/
theorem infinite_psd_of_finite (c : InfiniteOverlapCoordinates)
    (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m) :
    (Matrix.of c).PosSemidef := by
  classical
  constructor
  · ext i j
    let m := max i j + 1
    have hi : i < m := by omega
    have hj : j < m := by omega
    have hh := (hc m).isHermitian.apply (⟨i, hi⟩ : Fin m) (⟨j, hj⟩ : Fin m)
    simpa [Matrix.conjTranspose_apply, infiniteTruncate] using hh
  · intro x
    let m := x.support.sup id + 1
    let e : Fin m ↪ ℕ := Fin.valEmbedding
    have hsup (k : ℕ) (hk : k ∈ x.support) : k < m := by
      dsimp [m]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
    have hxrange : (x.support : Set ℕ) ⊆ Set.range e := by
      intro k hk
      exact ⟨⟨k, hsup k hk⟩, rfl⟩
    let y : Fin m →₀ ℝ := Finsupp.comapDomain e x e.injective.injOn
    have hxy : y.embDomain e = x := Finsupp.embDomain_comapDomain hxrange
    have hbase := (hc m).2 y
    rw [← hxy]
    simp only [Finsupp.embDomain_eq_mapDomain]
    simpa [e, Finsupp.sum_mapDomain_index, Matrix.of_apply, infiniteTruncate,
      mul_add, add_mul, mul_assoc] using hbase

/-- Finite Gram positivity plus unit diagonals produce a coherent sequence
of unit vectors in one complete real Hilbert space. -/
theorem infinite_gram_unit_of_finite (c : InfiniteOverlapCoordinates)
    (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m)
    (hd : ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (v : ℕ → H),
      (∀ i j, inner ℝ (v i) (v j) = c i j) ∧
      (∀ i, ‖v i‖ = 1) := by
  obtain ⟨H, hN, hI, hC, v, hv⟩ :=
    scalarKernel_gram (Matrix.of c) (infinite_psd_of_finite c hc)
  refine ⟨H, hN, hI, hC, v, ?_, ?_⟩
  · intro i j
    exact hv i j
  · intro i
    have hh := (hd (i+1)) (⟨i, Nat.lt_succ_self i⟩ : Fin (i+1))
    have hdiag : c i i = 1 := by
      simpa only [fullUnitDiagonal, Set.mem_ofPred_eq, infiniteTruncate] using hh
    have hnorm : ‖v i‖ ^ 2 = 1 := by
      simpa [real_inner_self_eq_norm_sq] using (hv i i).trans hdiag
    nlinarith [norm_nonneg (v i)]

/-- Actual physical infinite-array weak-limit laws are almost surely
coherent Hilbert-space Gram laws on unit vectors. -/
theorem physicalInfiniteAsymptoticLimit_hilbert_gram
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift.physicalInfiniteAsymptoticLimitSet μ β) :
    ∀ᵐ c ∂(ρ : MeasureTheory.Measure InfiniteOverlapCoordinates),
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (v : ℕ → H),
        (∀ i j, inner ℝ (v i) (v j) = c i j) ∧
        (∀ i, ‖v i‖ = 1) := by
  filter_upwards [
    SlowEquilibration.PureCapturePhysicalInfiniteDSInput.physicalInfiniteAsymptoticLimit_gram μ β hρ,
    SlowEquilibration.PureCapturePhysicalInfiniteDSInput.physicalInfiniteAsymptoticLimit_unitDiagonal μ β hρ]
    with c hc hd
  exact infinite_gram_unit_of_finite c hc hd

end SlowEquilibration.PureCapturePhysicalInfiniteGramRealization
