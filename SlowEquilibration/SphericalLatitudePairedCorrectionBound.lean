-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePairedCorrection

/-! Genuine uniform normalized radial derivative envelope for the finite
higher latitude Wick corrections, assembled from the actual original
Gaussian tensor banks. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalAging.FiniteModel FiniteWickPairings SphericalUniformWickMoments
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem abs_list_sum_le_bounds {ι : Type*} (T : List ι) (f g : ι→ℝ)
    (h : ∀ k∈T,|f k|≤g k) : |(T.map f).sum|≤(T.map g).sum := by
  induction T with
  | nil => simp
  | cons k T ih =>
    simp only [List.map_cons,List.sum_cons]
    apply (abs_add_le _ _).trans
    exact add_le_add (h k (by simp)) (ih (fun l hl => h l (by simp [hl])))

/-- Literal finite original-bank envelope, with a constant depending only
on the fixed degree in every coefficient multiplying each Gaussian bank. -/
def latitudeCorrectionEnvelope (n p : ℕ) (J : SphericalAging.FiniteModel.Disorder (n+1) p) : ℝ :=
  ∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
    ((labeledWickPairings S).attach.map (fun L => (2 : ℝ)^L.val.length*(p : ℝ)*
      latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J)).sum

/-- One actual Wick derivative term has the genuine original projected bank envelope. -/
theorem normalized_weighted_latitude_pairing_derivative_abs_le {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    |(1-r^2)/Real.sqrt (n+1 : ℕ)*(latitudeEvenWickCoefficient n L.length*
        deriv (radialWickMonomial (Finset.univ\S).card L.length) r*latitudePairingContraction n p J u S L)|≤
      (2 : ℝ)^L.length*(p : ℝ)*latitudePairingEnvelope n p S L hL J := by
  have hc := latitudeEvenWickCoefficient_mem hn L.length
  have hcoeff : |latitudeEvenWickCoefficient n L.length|≤(2 : ℝ)^L.length := by
    rw [abs_of_nonneg hc.1]
    exact hc.2
  have hrad : |(1-r^2)*deriv (radialWickMonomial (Finset.univ\S).card L.length) r|≤(p : ℝ) := by
    have h := weighted_radialWickMonomial_derivative_abs_le (Finset.univ\S).card L.length hr
    have hdegree : ((Finset.univ\S).card : ℝ)+(L.length : ℝ)+(L.length : ℝ)=p := by
      exact_mod_cast valid_pairing_degree hL
    linarith
  have hpair := latitudePairingContraction_abs_le_envelope_onSphere hn S L hL J u hu
  have he : (1-r^2)/Real.sqrt (n+1 : ℕ)*(latitudeEvenWickCoefficient n L.length*
      deriv (radialWickMonomial (Finset.univ\S).card L.length) r*latitudePairingContraction n p J u S L)=
      latitudeEvenWickCoefficient n L.length*
        ((1-r^2)*deriv (radialWickMonomial (Finset.univ\S).card L.length) r)*
        (latitudePairingContraction n p J u S L/Real.sqrt (n+1 : ℕ)) := by ring
  rw [he,abs_mul,abs_mul]
  exact mul_le_mul (mul_le_mul hcoeff hrad (abs_nonneg _)
    (pow_nonneg (by norm_num : (0 : ℝ)≤2) _)) hpair (abs_nonneg _)
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ)≤2) _) (Nat.cast_nonneg p))

/-- Actual full higher correction derivative is uniformly bounded in the
physical axis and latitude, by a literal original-disorder Gaussian envelope. -/
theorem normalized_weighted_pairedLatitudeCorrection_derivative_abs_le {n p : ℕ} (hn : 1≤n)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    |(1-r^2)/Real.sqrt (n+1 : ℕ)*deriv (pairedLatitudeCorrection n p J u) r|≤
      latitudeCorrectionEnvelope n p J := by
  rw [(pairedLatitudeCorrection_hasDerivAt n p J u r).deriv]
  unfold latitudeCorrectionEnvelope
  simp_rw [Finset.mul_sum,←List.sum_map_mul_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  have he : ((labeledWickPairings S).attach.map (fun L =>
      (1-r^2)/Real.sqrt (n+1 : ℕ)*(latitudeEvenWickCoefficient n L.val.length*
        deriv (radialWickMonomial (Finset.univ\S).card L.val.length) r*latitudePairingContraction n p J u S L.val))).sum=
      ((labeledWickPairings S).map (fun L =>
        (1-r^2)/Real.sqrt (n+1 : ℕ)*(latitudeEvenWickCoefficient n L.length*
          deriv (radialWickMonomial (Finset.univ\S).card L.length) r*latitudePairingContraction n p J u S L))).sum := by
    exact congrArg List.sum (List.attach_map_val
      (l := labeledWickPairings S)
      (f := fun L => (1-r^2)/Real.sqrt (n+1 : ℕ)*(latitudeEvenWickCoefficient n L.length*
        deriv (radialWickMonomial (Finset.univ\S).card L.length) r*latitudePairingContraction n p J u S L)))
  rw [←he]
  apply abs_list_sum_le_bounds
  intro L hL
  exact normalized_weighted_latitude_pairing_derivative_abs_le hn S L.val
    (labeledWickPairings_valid S L.val L.property) J u hu hr

end
end SlowEquilibration.SphericalLatitudeTensorMoments
