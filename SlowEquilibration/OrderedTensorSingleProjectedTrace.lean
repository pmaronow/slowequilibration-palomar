-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OrderedTensorTraceRegularity

/-! Literal coordinate grouping of one Π_x contraction of the original
ordered tensor. The Kronecker part is the actual fixed-slot trace bank;
the rank-one part is the original physical Hamiltonian divided by N. -/

@[expose] public section
namespace SlowEquilibration.OrderedTensorTraceGaussianBank
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalAging.FiniteModel
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fullTensorIndex {N q j : ℕ} (a : TensorIndex N q) (b c : TensorIndex N j) :
    TensorIndex N (q+j+j) := Fin.addCases (Fin.addCases a b) c

def fullTensorIndexEquiv (N q j : ℕ) :
    ((TensorIndex N q × TensorIndex N j) × TensorIndex N j) ≃ TensorIndex N (q+j+j) where
  toFun z := fullTensorIndex z.1.1 z.1.2 z.2
  invFun I := ((fun k => I (Fin.castAdd j (Fin.castAdd j k)),
    fun k => I (Fin.castAdd j (Fin.natAdd q k))),fun k => I (Fin.natAdd (q+j) k))
  left_inv z := by
    rcases z with ⟨⟨a,b⟩,c⟩
    apply Prod.ext
    · apply Prod.ext <;> funext k <;> simp only [fullTensorIndex,Fin.addCases_left,Fin.addCases_right]
    · funext k
      simp only [fullTensorIndex,Fin.addCases_right]
  right_inv I := by
    funext k
    refine Fin.addCases (fun l => ?_) (fun h => ?_) k
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) l
      · simp only [fullTensorIndex,Fin.addCases_left]
      · simp only [fullTensorIndex,Fin.addCases_left,Fin.addCases_right]
    · simp only [fullTensorIndex,Fin.addCases_right]

/-- Exact original coefficient indexing as independent free and paired slots. -/
theorem sum_original_tensorIndex (N q j : ℕ) (F : TensorIndex N (q+j+j) → ℝ) :
    (∑ I,F I)=∑ a : TensorIndex N q,∑ b : TensorIndex N j,∑ c : TensorIndex N j,
      F (fullTensorIndex a b c) := by
  have h := Fintype.sum_equiv (fullTensorIndexEquiv N q j)
    (fun z => F (fullTensorIndex z.1.1 z.1.2 z.2)) F (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h.symm

theorem tensorMonomial_fullTensorIndex {N q j : ℕ} (x : Vector N)
    (a : TensorIndex N q) (b c : TensorIndex N j) :
    tensorMonomial x (fullTensorIndex a b c)=
      tensorMonomial x a*tensorMonomial x b*tensorMonomial x c := by
  unfold tensorMonomial
  rw [Fin.prod_univ_add,Fin.prod_univ_add]
  simp only [fullTensorIndex,Fin.addCases_left,Fin.addCases_right]

def singleTraceProjectionEntry {N : ℕ} (x : Vector N) (b c : TensorIndex N 1) : ℝ :=
  (if b=c then 1 else 0)-tensorMonomial x b*tensorMonomial x c/(N : ℝ)

/-- The one-pair coefficient is the literal physical Π_x matrix entry. -/
theorem singleTraceProjectionEntry_eq {N : ℕ} (x : Vector N) (b c : TensorIndex N 1) :
    singleTraceProjectionEntry x b c=(if b 0=c 0 then 1 else 0)-x (b 0)*x (c 0)/(N : ℝ) := by
  have he : b=c ↔ b 0=c 0 := by
    constructor
    · intro h;rw [h]
    · intro h;funext k;have hk : k=0 := Subsingleton.elim _ _;simpa only [hk] using h
  simp only [singleTraceProjectionEntry,tensorMonomial,Fin.prod_univ_one,he]

def singleProjectedTracedHamiltonian (N q : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+1+1)) (x : Vector N) : ℝ :=
  normalization N (q+1+1)*∑ a : TensorIndex N q,∑ b : TensorIndex N 1,∑ c : TensorIndex N 1,
    J (fullTensorIndex a b c)*tensorMonomial x a*singleTraceProjectionEntry x b c

/-- Exact Π_x-to-original-trace grouping, proved at every original sample. -/
theorem singleProjectedTracedHamiltonian_eq (N q : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+1+1)) (x : Vector N) :
    singleProjectedTracedHamiltonian N q J x=
      tracedHamiltonian N q 1 J x-Hamiltonian N (q+1+1) J x/(N : ℝ) := by
  classical
  have hdelta (a : TensorIndex N q) (b : TensorIndex N 1) :
      (∑ c : TensorIndex N 1,J (fullTensorIndex a b c)*tensorMonomial x a*(if b=c then 1 else 0))=
        J (tracedIndex a b)*tensorMonomial x a := by
    simp only [mul_ite,mul_one,mul_zero]
    rw [Fintype.sum_ite_eq]
    rfl
  have hH : Hamiltonian N (q+1+1) J x=
      normalization N (q+1+1)*∑ a : TensorIndex N q,∑ b : TensorIndex N 1,∑ c : TensorIndex N 1,
        J (fullTensorIndex a b c)*tensorMonomial x a*tensorMonomial x b*tensorMonomial x c := by
    unfold Hamiltonian
    rw [sum_original_tensorIndex N q 1]
    simp_rw [tensorMonomial_fullTensorIndex,mul_assoc]
  have hrank (a : TensorIndex N q) (b c : TensorIndex N 1) :
      J (fullTensorIndex a b c)*tensorMonomial x a*
        (tensorMonomial x b*tensorMonomial x c/(N : ℝ))=
      (J (fullTensorIndex a b c)*tensorMonomial x a*tensorMonomial x b*tensorMonomial x c)/(N : ℝ) := by ring
  unfold singleProjectedTracedHamiltonian singleTraceProjectionEntry
  simp_rw [mul_sub,Finset.sum_sub_distrib,hdelta,hrank,←Finset.sum_div]
  rw [hH]
  unfold tracedHamiltonian
  simp only [tensorMonomial]
  simp_rw [Finset.sum_mul]
  ring

/-- The literal one-pair projection contraction is controlled uniformly
by the actual original trace and original Hamiltonian regularity events. -/
theorem singleProjectedTracedHamiltonian_abs_le_of_regular {N q : ℕ}
    (hN : 0 < N) (hq : 1 ≤ q)
    (J : SphericalAging.FiniteModel.Disorder N (q+1+1)) (C : ℝ)
    (htrace : traceLandscapeNorm N q 1 (Equiv.refl _) J ≤ C)
    (hraw : SphericalAging.GaussianLandscape.landscapeNorm N (q+1+1) J ≤ C)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    |singleProjectedTracedHamiltonian N q J x| ≤ C*(N : ℝ)^(1-(1 : ℝ)/2)+C := by
  have hp : 1 ≤ q+1+1 := by omega
  have ht := permutedTracedHamiltonian_abs_le_of_traceRegular hN hq 1 (Equiv.refl _) J C htrace x hx
  have hperm : permutedTensor (N := N) (Equiv.refl (Fin (q+1+1))) J=J := by
    funext I
    rw [permutedTensor_apply]
    rfl
  change |tracedHamiltonian N q 1 (permutedTensor (Equiv.refl _) J) x| ≤ _ at ht
  rw [hperm] at ht
  simp only [Nat.cast_one] at ht
  have hH := (SphericalAging.HamiltonianBallBounds.Hamiltonian_ball_bound hN hp J hx).trans hraw
  rw [singleProjectedTracedHamiltonian_eq]
  apply (abs_sub _ _).trans
  apply add_le_add ht
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [abs_div,abs_of_pos hNr]
  exact hH

/-- Source-scale normalization turns a one-pair projection correction into
a true dimension-uniform bound on its genuine joint regularity event. -/
theorem normalized_singleProjectedTracedHamiltonian_abs_le {N q : ℕ}
    (hN : 0 < N) (hq : 1 ≤ q)
    (J : SphericalAging.FiniteModel.Disorder N (q+1+1)) (C : ℝ)
    (hC : 0 ≤ C) (htrace : traceLandscapeNorm N q 1 (Equiv.refl _) J ≤ C)
    (hraw : SphericalAging.GaussianLandscape.landscapeNorm N (q+1+1) J ≤ C)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    |singleProjectedTracedHamiltonian N q J x|/Real.sqrt N ≤ 2*C := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)]
    exact_mod_cast hN
  have hnroot : (N : ℝ)^(1-(1 : ℝ)/2)=Real.sqrt N := by
    norm_num only
    rw [Real.sqrt_eq_rpow]
  apply (div_le_iff₀ hs).mpr
  have h := singleProjectedTracedHamiltonian_abs_le_of_regular hN hq J C htrace hraw x hx
  rw [hnroot] at h
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hs1 hC])

/-- A fixed-degree constant chosen before the dimension or original sample. -/
def singleProjectionThreshold (q : ℕ) : ℝ :=
  max (SphericalAging.GaussianLandscape.landscapeThreshold q+4)
    (SphericalAging.GaussianLandscape.landscapeThreshold (q+1+1)+4)

def singleProjectionRegular (N q : ℕ) : Set (SphericalAging.FiniteModel.Disorder N (q+1+1)) :=
  {J | traceLandscapeNorm N q 1 (Equiv.refl _) J ≤ singleProjectionThreshold q ∧
    SphericalAging.GaussianLandscape.landscapeNorm N (q+1+1) J ≤ singleProjectionThreshold q}

/-- Genuine exceptional probability for the concrete joint original/trace
regularity event, with degree chosen before dimension. -/
theorem singleProjectionRegular_failure_probability {N q : ℕ} (hN : 2 ≤ N) (hq : 0 < q) :
    (SphericalAging.FiniteModel.disorderLaw N (q+1+1)).real {J | J∉singleProjectionRegular N q} ≤
      2*Real.exp (-(N : ℝ)) := by
  have hsub : {J : SphericalAging.FiniteModel.Disorder N (q+1+1) | J∉singleProjectionRegular N q} ⊆
      {J | SphericalAging.GaussianLandscape.landscapeThreshold q+4 < traceLandscapeNorm N q 1 (Equiv.refl _) J} ∪
      {J | SphericalAging.GaussianLandscape.landscapeThreshold (q+1+1)+4 <
        SphericalAging.GaussianLandscape.landscapeNorm N (q+1+1) J} := by
    intro J hJ
    change ¬(_ ∧ _) at hJ
    rcases not_and_or.mp hJ with htrace|hraw
    · exact Or.inl (lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge htrace))
    · exact Or.inr (lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hraw))
  apply ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
  have ht := traceLandscapeNorm_failure_probability hN hq 1 (Equiv.refl _)
  have hr := SphericalAging.GaussianLandscape.landscape_exponential_dimension_bound
    (p := q+1+1) hN (by omega : 0 < q+1+1)
  simpa only [two_mul] using add_le_add ht hr

/-- Uniform physical one-pair projection bound on its actual exponentially
probable original-tensor event, with no supremum or mean hypothesis. -/
theorem normalized_singleProjectedTracedHamiltonian_abs_le_on_event {N q : ℕ}
    (hN : 0 < N) (hq : 1 ≤ q)
    (J : SphericalAging.FiniteModel.Disorder N (q+1+1)) (hJ : J∈singleProjectionRegular N q)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    |singleProjectedTracedHamiltonian N q J x|/Real.sqrt N ≤ 2*singleProjectionThreshold q := by
  apply normalized_singleProjectedTracedHamiltonian_abs_le hN hq J _ _ hJ.1 hJ.2 x hx
  apply (SphericalAging.GaussianLandscape.landscapeThreshold_pos q).le.trans
  exact (show SphericalAging.GaussianLandscape.landscapeThreshold q ≤
    SphericalAging.GaussianLandscape.landscapeThreshold q+4 by linarith).trans (le_max_left _ _)

end
end SlowEquilibration.OrderedTensorTraceGaussianBank
