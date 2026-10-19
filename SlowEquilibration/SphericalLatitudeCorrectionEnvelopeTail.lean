-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCorrectionEnvelopeMean

/-! An actual dimension-uniform exponential failure bound for the entire
higher latitude Wick correction envelope. The finite bank count and
threshold depend only on the fixed degree, before dimension is chosen. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set FiniteWickPairings
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem measure_exists_list_le {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (T : List ι) (A : ι→Set Ω) (c : ℝ≥0∞)
    (hA : ∀ a∈T,ν (A a)≤c) :
    ν {ω | ∃ a∈T,ω∈A a}≤(T.length : ℝ≥0∞)*c := by
  induction T with
  | nil => simp
  | cons a T ih =>
    have he : {ω | ∃ b∈a::T,ω∈A b}=A a∪{ω | ∃ b∈T,ω∈A b} := by
      ext ω
      simp only [List.mem_cons,Set.mem_ofPred_eq,Set.mem_union]
      aesop
    rw [he]
    apply (measure_union_le _ _).trans
    have h := add_le_add (hA a (by simp)) (ih (fun b hb => hA b (by simp [hb])))
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using h

private theorem list_sum_le_pointwise {ι : Type*} (T : List ι) (f g : ι→ℝ)
    (h : ∀ a∈T,f a≤g a) : (T.map f).sum≤(T.map g).sum := by
  induction T with
  | nil => simp
  | cons a T ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Literal number of actual original banks, depending only on degree. -/
def latitudeCorrectionBankCount (p : ℕ) : ℕ :=
  ∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),(labeledWickPairings S).length

/-- A fixed degree-only threshold for the literal correction envelope. -/
def latitudeCorrectionUniformConstant (p : ℕ) : ℝ :=
  ∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
    ((labeledWickPairings S).attach.map (fun L => (2 : ℝ)^L.val.length*(p : ℝ)*
      (2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))+1))).sum

/-- Actual bad-bank event, shared by every physical axis and every latitude. -/
def latitudeCorrectionBadBanks (n p : ℕ) : Set (SphericalAging.FiniteModel.Disorder (n+1) p) :=
  ⋃ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
    {J | ∃ L∈(labeledWickPairings S).attach,
      2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))+1≤
        latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J}

/-- Outside the genuine finite bad-bank union, the entire correction
has a uniform deterministic bound for the original coefficient sample. -/
theorem latitudeCorrectionEnvelope_le_of_not_badBanks {n p : ℕ}
    (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (hJ : J∉latitudeCorrectionBadBanks n p) :
    latitudeCorrectionEnvelope n p J≤latitudeCorrectionUniformConstant p := by
  unfold latitudeCorrectionEnvelope latitudeCorrectionUniformConstant
  apply Finset.sum_le_sum
  intro S hS
  apply list_sum_le_pointwise
  intro L hL
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_lt
  apply lt_of_not_ge
  intro h
  apply hJ
  exact Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨hS,⟨L,hL,h⟩⟩⟩

/-- The genuine original Gaussian measure of the entire bad-bank union
is exponentially small, with no supplied mean or event hypothesis. -/
theorem latitudeCorrectionBadBanks_probability {n p : ℕ} (hn : 1≤n) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p (latitudeCorrectionBadBanks n p)≤
      (latitudeCorrectionBankCount p : ℝ≥0∞)*
        ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
  unfold latitudeCorrectionBadBanks
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _≤∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
        ((labeledWickPairings S).length : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
      apply Finset.sum_le_sum
      intro S hS
      have he := measure_exists_list_le (SphericalAging.FiniteModel.disorderLaw (n+1) p)
        (labeledWickPairings S).attach
        (fun L => {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))+1≤
          latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J})
        (ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2))) (by
          intro L hL
          have hj := nonempty_Wick_pairing_length_pos (Finset.mem_erase.mp hS).1 L.property
          simpa only [one_pow,neg_one_mul] using latitudePairingEnvelope_upper_tail hn S L.val
            (labeledWickPairings_valid S L.val L.property) hj (s := 1) (by norm_num))
      convert he using 1
      · congr 1
      · simp only [List.length_attach]
    _=_ := by rw [←Finset.sum_mul];simp only [latitudeCorrectionBankCount,Nat.cast_sum]

/-- The literal full correction envelope itself has the same actual
original-disorder exponential failure bound. -/
theorem latitudeCorrectionEnvelope_uniform_upper_tail {n p : ℕ} (hn : 1≤n) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p
      {J | latitudeCorrectionUniformConstant p<latitudeCorrectionEnvelope n p J}≤
      (latitudeCorrectionBankCount p : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
  apply (measure_mono (show {J | latitudeCorrectionUniformConstant p<latitudeCorrectionEnvelope n p J}⊆
      latitudeCorrectionBadBanks n p from ?_)).trans (latitudeCorrectionBadBanks_probability hn)
  intro J hJ
  by_contra h
  exact (not_lt_of_ge (latitudeCorrectionEnvelope_le_of_not_badBanks J h)) hJ

end
end SlowEquilibration.SphericalLatitudeTensorMoments
