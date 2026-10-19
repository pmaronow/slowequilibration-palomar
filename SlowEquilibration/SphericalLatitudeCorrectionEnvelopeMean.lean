-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePairedCorrectionBound

/-! The literal finite original Gaussian-bank correction envelope has a
true finite mean bounded by a fixed degree-only constant before n is chosen. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory FiniteWickPairings
open SphericalAging.FiniteModel
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integrable_list_sum {Ω ι : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (T : List ι) (f : ι→Ω→ℝ) (hi : ∀ a∈T,Integrable (f a) ν) :
    Integrable (fun ω => (T.map (fun a => f a ω)).sum) ν := by
  induction T with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    convert integrable_zero Ω ℝ ν using 1
  | cons a T ih =>
    simp only [List.map_cons,List.sum_cons]
    convert (hi a (by simp)).add (ih (fun b hb => hi b (by simp [hb]))) using 1

private theorem integral_list_sum {Ω ι : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (T : List ι) (f : ι→Ω→ℝ) (hi : ∀ a∈T,Integrable (f a) ν) :
    (∫ ω,(T.map (fun a => f a ω)).sum ∂ν)=(T.map (fun a => ∫ ω,f a ω ∂ν)).sum := by
  induction T with
  | nil => simp
  | cons a T ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hi a (by simp)) (integrable_list_sum ν T f (fun b hb => hi b (by simp [hb])))]
    rw [ih (fun b hb => hi b (by simp [hb]))]

private theorem list_sum_le_of_pointwise {ι : Type*} (T : List ι) (f g : ι→ℝ)
    (h : ∀ a∈T,f a≤g a) : (T.map f).sum≤(T.map g).sum := by
  induction T with
  | nil => simp
  | cons a T ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Fixed before the physical dimension: the genuine finite Wick list
and its actual vector/pair Gaussian comparison constants. -/
def latitudeCorrectionMeanConstant (p : ℕ) : ℝ :=
  ∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
    ((labeledWickPairings S).attach.map (fun L => (2 : ℝ)^L.val.length*(p : ℝ)*
      (2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))))).sum

theorem latitudeCorrectionEnvelope_integrable {n p : ℕ} (hn : 1≤n) :
    Integrable (latitudeCorrectionEnvelope n p) (SphericalAging.FiniteModel.disorderLaw (n+1) p) := by
  unfold latitudeCorrectionEnvelope
  apply integrable_finsetSum
  intro S hS
  apply integrable_list_sum
  intro L hL
  exact (latitudePairingEnvelope_integrable hn S L.val
    (labeledWickPairings_valid S L.val L.property)).const_mul _

/-- The true expected entire correction envelope is bounded uniformly
in dimension, with no asserted latitude-mean or probability-limit input. -/
theorem expected_latitudeCorrectionEnvelope_le {n p : ℕ} (hn : 1≤n) :
    (∫ J,latitudeCorrectionEnvelope n p J ∂SphericalAging.FiniteModel.disorderLaw (n+1) p)≤
      latitudeCorrectionMeanConstant p := by
  have hi (S : Finset (Fin p)) :
      ∀ L∈(labeledWickPairings S).attach,Integrable
        (fun J : SphericalAging.FiniteModel.Disorder (n+1) p => (2 : ℝ)^L.val.length*(p : ℝ)*
          latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J)
        (SphericalAging.FiniteModel.disorderLaw (n+1) p) := by
    intro L hL
    exact (latitudePairingEnvelope_integrable hn S L.val
      (labeledWickPairings_valid S L.val L.property)).const_mul _
  unfold latitudeCorrectionEnvelope latitudeCorrectionMeanConstant
  rw [integral_finsetSum _ (fun S hS => integrable_list_sum _ _ _ (hi S))]
  apply Finset.sum_le_sum
  intro S hS
  rw [integral_list_sum _ _ _ (hi S)]
  apply list_sum_le_of_pointwise
  intro L hL
  rw [integral_const_mul]
  have hSne : S≠∅ := (Finset.mem_erase.mp hS).1
  have hj := nonempty_Wick_pairing_length_pos hSne L.property
  have he := expected_latitudePairingEnvelope_le hn S L.val
    (labeledWickPairings_valid S L.val L.property) hj
  have hpow : ((n+1 : ℕ) : ℝ)^((1-(L.val.length : ℝ))/2)≤1 := by
    have hjr : (1 : ℝ)≤L.val.length := by exact_mod_cast hj
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1≤n+1 by omega)) (by linarith)
  have he' : (∫ J,latitudePairingEnvelope n p S L.val
      (labeledWickPairings_valid S L.val L.property) J ∂SphericalAging.FiniteModel.disorderLaw (n+1) p)≤
      2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ)) :=
    he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (by positivity))
  exact mul_le_mul_of_nonneg_left he' (by positivity)

end
end SlowEquilibration.SphericalLatitudeTensorMoments
