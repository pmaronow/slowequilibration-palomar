-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalInfiniteDSInput
public import SlowEquilibration.PureCapturePhysicalInfiniteGramRealization
public import OverlapPaper.DovbyshSudakov
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! Transport a physical countable full Gram array to the off-diagonal
array type used by the constructive Dovbysh--Sudakov theorem. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalDSOffDiagonalTransport

open MeasureTheory ProbabilityTheory InnerProductSpace
open SlowEquilibration SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness
open SlowEquilibration.PureCapturePhysicalInfiniteDSInput
open SlowEquilibration.PureCapturePhysicalInfiniteGramRealization
open SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

def clipOverlap (x : ℝ) : Set.Icc (-1 : ℝ) 1 :=
  ⟨max (-1) (min 1 x),
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

theorem clipOverlap_eq (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (clipOverlap x : ℝ) = x := by
  simp [clipOverlap, hx.1, hx.2]

theorem continuous_clipOverlap : Continuous clipOverlap := by
  apply Continuous.subtype_mk
  fun_prop

def toOffDiagonal (c : InfiniteOverlapCoordinates) : OverlapPaper.OverlapArray :=
  fun ij => clipOverlap (c ij.1.1 ij.1.2)

theorem continuous_toOffDiagonal : Continuous toOffDiagonal := by
  apply continuous_pi
  intro ij
  exact continuous_clipOverlap.comp
    ((continuous_apply ij.1.2).comp (continuous_apply ij.1.1))

theorem fullGram_entry_mem_Icc (c : InfiniteOverlapCoordinates)
    (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m)
    (hd : ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m)
    (i j : ℕ) : c i j ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨H, hN, hI, hC, v, hv, hn⟩ :=
    infinite_gram_unit_of_finite c hc hd
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℝ H := hI
  have h := abs_real_inner_le_norm (v i) (v j)
  rw [hv i j, hn i, hn j, one_mul] at h
  exact ⟨(neg_le_of_abs_le h), (le_of_abs_le h)⟩

theorem completeArray_toOffDiagonal (c : InfiniteOverlapCoordinates)
    (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m)
    (hd : ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m)
    (i j : ℕ) : OverlapPaper.completeArray (toOffDiagonal c) i j = c i j := by
  by_cases hij : i < j
  · rw [OverlapPaper.completeArray_of_lt _ hij]
    exact clipOverlap_eq _ (fullGram_entry_mem_Icc c hc hd i j)
  · by_cases hji : j < i
    · rw [OverlapPaper.completeArray_of_gt _ hji]
      have hsym := (infinite_psd_of_finite c hc).isHermitian.apply i j
      have hsym' : c j i = c i j := by
        simpa [Matrix.conjTranspose_apply] using hsym
      change (clipOverlap (c j i) : ℝ) = c i j
      rw [clipOverlap_eq _ (fullGram_entry_mem_Icc c hc hd j i), hsym']
    · have he : i = j := by omega
      subst j
      have hh := hd (i+1) (⟨i, Nat.lt_succ_self i⟩ : Fin (i+1))
      have hh' : c i i = 1 := by
        simpa only [fullUnitDiagonal, Set.mem_ofPred_eq, infiniteTruncate] using hh
      simpa using hh'.symm

theorem toOffDiagonal_mem_GramArrays (c : InfiniteOverlapCoordinates)
    (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m)
    (hd : ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m) :
    toOffDiagonal c ∈ OverlapPaper.GramArrays := by
  intro m
  have he : OverlapPaper.principalMatrix (toOffDiagonal c) m =
      Matrix.of (infiniteTruncate m c) := by
    ext i j
    exact completeArray_toOffDiagonal c hc hd i j
  rw [he]
  exact hc m

/-- The transported law satisfies the exact Gram-support premise of the
constructive Dovbysh--Sudakov theorem. -/
theorem physicalOffDiagonalLaw_gram
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    (((ρ.map toOffDiagonal : ProbabilityMeasure OverlapPaper.OverlapArray) :
      Measure OverlapPaper.OverlapArray) OverlapPaper.GramArrays) = 1 := by
  have hgood : ∀ᵐ c ∂(ρ : Measure InfiniteOverlapCoordinates),
      toOffDiagonal c ∈ OverlapPaper.GramArrays := by
    filter_upwards [physicalInfiniteAsymptoticLimit_gram μ β hρ,
      physicalInfiniteAsymptoticLimit_unitDiagonal μ β hρ] with c hc hd
    exact toOffDiagonal_mem_GramArrays c hc hd
  have hmap : ∀ᵐ R ∂((ρ.map toOffDiagonal :
      ProbabilityMeasure OverlapPaper.OverlapArray) : Measure OverlapPaper.OverlapArray),
      R ∈ OverlapPaper.GramArrays :=
    (ae_map_iff continuous_toOffDiagonal.measurable.aemeasurable
      OverlapPaper.isClosed_GramArrays.measurableSet).mpr hgood
  exact (mem_ae_iff_prob_eq_one OverlapPaper.isClosed_GramArrays.measurableSet).mp hmap

theorem finiteSupportPermutation_extend (σ : Equiv.Perm ℕ)
    (hs : ({i | σ i ≠ i} : Set ℕ).Finite) :
    ∃ n, ∃ e : Equiv.Perm (Fin n), σ = OverlapPaper.extendFinitePermutation e := by
  classical
  let s : Finset ℕ := hs.toFinset
  let n := s.sup id + 1
  have hfix (i : ℕ) (hi : n ≤ i) : σ i = i := by
    by_contra hh
    have his : i ∈ s := by simpa [s] using (show i ∈ ({j | σ j ≠ j} : Set ℕ) from hh)
    have hib : i ≤ s.sup id := by simpa using (Finset.le_sup (f := id) his)
    omega
  have hbound (i : ℕ) (hi : i < n) : σ i < n := by
    by_contra hh
    have hσfix := hfix (σ i) (Nat.le_of_not_gt hh)
    have hsame : σ i = i := σ.injective hσfix
    omega
  have hboundInv (i : ℕ) (hi : i < n) : σ.symm i < n := by
    by_contra hh
    have hσfix := hfix (σ.symm i) (Nat.le_of_not_gt hh)
    have hsame : i = σ.symm i := by simpa using hσfix
    omega
  let e : Equiv.Perm (Fin n) := {
    toFun := fun i => ⟨σ i.val, hbound i.val i.isLt⟩
    invFun := fun i => ⟨σ.symm i.val, hboundInv i.val i.isLt⟩
    left_inv := by intro i; apply Fin.ext; simp
    right_inv := by intro i; apply Fin.ext; simp
  }
  refine ⟨n, e, ?_⟩
  apply Equiv.ext
  intro i
  by_cases hi : i < n
  · simpa [e] using (OverlapPaper.extendFinitePermutation_apply_fin e (⟨i, hi⟩ : Fin n)).symm
  · simpa [hfix i (Nat.le_of_not_gt hi)] using
      (OverlapPaper.extendFinitePermutation_apply_ge (i := i) e (Nat.le_of_not_gt hi)).symm

def prefixPermutation (σ : Equiv.Perm ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → σ i = i) : Equiv.Perm (Fin n) := by
  have hbound (i : ℕ) (hi : i < n) : σ i < n := by
    by_contra hh
    have hσfix := hfix (σ i) (Nat.le_of_not_gt hh)
    have hsame : σ i = i := σ.injective hσfix
    omega
  have hboundInv (i : ℕ) (hi : i < n) : σ.symm i < n := by
    by_contra hh
    have hσfix := hfix (σ.symm i) (Nat.le_of_not_gt hh)
    have hsame : i = σ.symm i := by simpa using hσfix
    omega
  exact {
    toFun := fun i => ⟨σ i.val, hbound i.val i.isLt⟩
    invFun := fun i => ⟨σ.symm i.val, hboundInv i.val i.isLt⟩
    left_inv := by intro i; apply Fin.ext; simp
    right_inv := by intro i; apply Fin.ext; simp
  }

@[simp] theorem prefixPermutation_apply (σ : Equiv.Perm ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → σ i = i) (i : Fin n) :
    ((prefixPermutation σ n hfix) i).val = σ i.val := rfl

theorem physicalOffDiagonalLaw_finite_exchangeable
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (σ : Equiv.Perm ℕ) (k : ℕ)
    (hfix : ∀ i, k ≤ i → σ i = i)
    (I : Finset OverlapPaper.ReplicaPair)
    (hI : ∀ ij ∈ I, ij.1.1 < k ∧ ij.1.2 < k) :
    (ρ : Measure InfiniteOverlapCoordinates).map
      (fun c => I.restrict (toOffDiagonal c)) =
    (ρ : Measure InfiniteOverlapCoordinates).map
      (fun c => I.restrict (OverlapPaper.arrayRelabel σ (toOffDiagonal c))) := by
  let e := prefixPermutation σ k hfix
  let F : FullOverlapCoordinates k →
      (I → Set.Icc (-1 : ℝ) 1) :=
    fun d => I.restrict (toOffDiagonal (padFullOverlap k d))
  have hF : Measurable F :=
    (Finset.measurable_restrict I).comp
      ((continuous_toOffDiagonal.comp (padFullOverlap_continuous k)).measurable)
  have hleft (c : InfiniteOverlapCoordinates) :
      F (infiniteTruncate k c) = I.restrict (toOffDiagonal c) := by
    funext ij
    apply Subtype.ext
    have hij := hI ij.1 ij.2
    simp [F, Finset.restrict, toOffDiagonal, padFullOverlap,
      infiniteTruncate, hij.1, hij.2]
  have hright (c : InfiniteOverlapCoordinates)
      (hc : ∀ m, infiniteTruncate m c ∈ fullGramCone m)
      (hd : ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m) :
      F (permuteFullOverlap e (infiniteTruncate k c)) =
        I.restrict (OverlapPaper.arrayRelabel σ (toOffDiagonal c)) := by
    funext ij
    apply Subtype.ext
    have hij := hI ij.1 ij.2
    simp only [F, Finset.restrict, toOffDiagonal, padFullOverlap,
      permuteFullOverlap, infiniteTruncate, hij.1, hij.2,
      dite_eq_left, OverlapPaper.arrayRelabel]
    change (clipOverlap (c (e ⟨ij.1.1.1, hij.1⟩).val
      (e ⟨ij.1.1.2, hij.2⟩).val) : ℝ) =
      OverlapPaper.completeArray (toOffDiagonal c)
        (σ ij.1.1.1) (σ ij.1.1.2)
    rw [prefixPermutation_apply, prefixPermutation_apply,
      clipOverlap_eq _ (fullGram_entry_mem_Icc c hc hd _ _),
      completeArray_toOffDiagonal c hc hd]
  have hgood : ∀ᵐ c ∂(ρ : Measure InfiniteOverlapCoordinates),
      (∀ m, infiniteTruncate m c ∈ fullGramCone m) ∧
      (∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m) := by
    filter_upwards [physicalInfiniteAsymptoticLimit_gram μ β hρ,
      physicalInfiniteAsymptoticLimit_unitDiagonal μ β hρ] with c hc hd
    exact ⟨hc, hd⟩
  have heq := physicalInfiniteAsymptoticLimit_exchangeable μ β hρ k e
  have heqM :
      (((ρ.map (infiniteTruncate k)).map (permuteFullOverlap e)).map F :
        Measure (I → Set.Icc (-1 : ℝ) 1)) =
      (((ρ.map (infiniteTruncate k)).map F) :
        Measure (I → Set.Icc (-1 : ℝ) 1)) :=
    congrArg (fun q : ProbabilityMeasure (FullOverlapCoordinates k) =>
      (q.map F : Measure (I → Set.Icc (-1 : ℝ) 1))) heq
  have hleftM :
      (ρ : Measure InfiniteOverlapCoordinates).map
        (fun c => I.restrict (toOffDiagonal c)) =
      (((ρ.map (infiniteTruncate k)).map F) :
        Measure (I → Set.Icc (-1 : ℝ) 1)) := by
    change (ρ : Measure InfiniteOverlapCoordinates).map
      (fun c => I.restrict (toOffDiagonal c)) =
      ((ρ : Measure InfiniteOverlapCoordinates).map (infiniteTruncate k)).map F
    rw [Measure.map_map hF (infiniteTruncate_continuous k).measurable]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun c => (hleft c).symm))
  have hrightM :
      (ρ : Measure InfiniteOverlapCoordinates).map
        (fun c => I.restrict (OverlapPaper.arrayRelabel σ (toOffDiagonal c))) =
      (((ρ.map (infiniteTruncate k)).map (permuteFullOverlap e)).map F :
        Measure (I → Set.Icc (-1 : ℝ) 1)) := by
    change (ρ : Measure InfiniteOverlapCoordinates).map
      (fun c => I.restrict (OverlapPaper.arrayRelabel σ (toOffDiagonal c))) =
      (((ρ : Measure InfiniteOverlapCoordinates).map (infiniteTruncate k)).map
        (permuteFullOverlap e)).map F
    rw [Measure.map_map hF (permuteFullOverlap_continuous e).measurable,
      Measure.map_map (hF.comp (permuteFullOverlap_continuous e).measurable)
        (infiniteTruncate_continuous k).measurable]
    exact Measure.map_congr (hgood.mono (fun c hc => (hright c hc.1 hc.2).symm))
  exact hleftM.trans (heqM.symm.trans hrightM.symm)

/-- The physical weak-limit law is weakly exchangeable after transport to
the off-diagonal array space. This uses its actual finite-matrix marginal
exchangeability and uniqueness of a product law from finite cylinders. -/
theorem physicalOffDiagonalLaw_exchangeable
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    OverlapPaper.WeaklyExchangeableOverlapLaw (ρ.map toOffDiagonal) := by
  intro σ hs
  obtain ⟨n, e, rfl⟩ := finiteSupportPermutation_extend σ hs
  let τ := OverlapPaper.extendFinitePermutation e
  have hτ : Continuous (fun c : InfiniteOverlapCoordinates =>
      OverlapPaper.arrayRelabel τ (toOffDiagonal c)) :=
    (OverlapPaper.continuous_arrayRelabel τ).comp continuous_toOffDiagonal
  have hmaps : (ρ : Measure InfiniteOverlapCoordinates).map
      (fun c => OverlapPaper.arrayRelabel τ (toOffDiagonal c)) =
      (ρ : Measure InfiniteOverlapCoordinates).map toOffDiagonal := by
    apply (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq
      hτ.measurable.aemeasurable
      continuous_toOffDiagonal.measurable.aemeasurable).2
    intro I
    let k := max n (I.sup (fun ij => max ij.1.1 ij.1.2) + 1)
    have hfix (i : ℕ) (hi : k ≤ i) : τ i = i :=
      OverlapPaper.extendFinitePermutation_apply_ge e (le_trans (le_max_left ..) hi)
    have hI (ij : OverlapPaper.ReplicaPair) (hij : ij ∈ I) :
        ij.1.1 < k ∧ ij.1.2 < k := by
      have hs := Finset.le_sup (f := fun ab : OverlapPaper.ReplicaPair =>
        max ab.1.1 ab.1.2) hij
      dsimp [k]
      constructor <;> omega
    exact (physicalOffDiagonalLaw_finite_exchangeable μ β hρ τ k hfix I hI).symm
  apply ProbabilityMeasure.toMeasure_injective
  change ((ρ.map toOffDiagonal).map (OverlapPaper.arrayRelabel τ) :
    Measure OverlapPaper.OverlapArray) =
    (ρ.map toOffDiagonal : Measure OverlapPaper.OverlapArray)
  change ((ρ : Measure InfiniteOverlapCoordinates).map toOffDiagonal).map
    (OverlapPaper.arrayRelabel τ) =
    (ρ : Measure InfiniteOverlapCoordinates).map toOffDiagonal
  rw [Measure.map_map (OverlapPaper.continuous_arrayRelabel τ).measurable
    continuous_toOffDiagonal.measurable]
  exact hmaps

/-- An unconditional random iid Hilbert-ball directing law for each actual
physical infinite-array limit. The directing law is the one constructed by
the proved `allLean` Dovbysh--Sudakov theorem. -/
theorem physicalInfiniteAsymptoticLimit_dovbyshSudakov
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    OverlapPaper.HasDovbyshSudakovRepresentation (ρ.map toOffDiagonal) :=
  OverlapPaper.dovbysh_sudakov (ρ.map toOffDiagonal)
    (physicalOffDiagonalLaw_gram μ β hρ)
    (physicalOffDiagonalLaw_exchangeable μ β hρ)

end SlowEquilibration.PureCapturePhysicalDSOffDiagonalTransport
