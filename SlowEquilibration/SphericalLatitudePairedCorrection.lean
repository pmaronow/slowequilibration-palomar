-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePairingGaussianBank

/-! Literal physical latitude mean separates into its exact unpaired
original Hamiltonian term and the true higher Wick corrections. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalAging.FiniteModel FiniteWickPairings SphericalUniformWickMoments
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairedLatitudeCorrection (n p : ℕ) (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (u : Vector (n+1)) (r : ℝ) : ℝ :=
  ∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
    ((labeledWickPairings S).map (fun L => latitudeEvenWickCoefficient n L.length*
      radialWickMonomial (Finset.univ\S).card L.length r*latitudePairingContraction n p J u S L)).sum

/-- The unpaired term is precisely r^p times the literal original Hamiltonian. -/
theorem pairedLatitudePolynomial_eq_leading_add_correction (n p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1)) (r : ℝ) :
    pairedLatitudePolynomial n p J u r=r^p*Hamiltonian (n+1) p J u+
      pairedLatitudeCorrection n p J u r := by
  unfold pairedLatitudePolynomial pairedLatitudeCorrection
  rw [←Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (Finset.empty_subset _))]
  congr 1
  rw [labeledWickPairings,dite_eq_right (by simp)]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_nil,
    latitudeEvenWickCoefficient,pow_zero,Nat.mul_zero,gaussianNormMoment_zero,div_one,radialWickMonomial,
    Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin,mul_one,one_mul,add_zero,
    latitudePairingContraction,pairingWeight,List.prod_nil]
  unfold Hamiltonian tensorMonomial
  ring

theorem pairedLatitudeCorrection_hasDerivAt (n p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1)) (r : ℝ) :
    HasDerivAt (pairedLatitudeCorrection n p J u)
      (∑ S∈((Finset.univ : Finset (Fin p)).powerset.erase ∅),
        ((labeledWickPairings S).map (fun L => latitudeEvenWickCoefficient n L.length*
          deriv (radialWickMonomial (Finset.univ\S).card L.length) r*
            latitudePairingContraction n p J u S L)).sum) r := by
  unfold pairedLatitudeCorrection
  apply HasDerivAt.fun_sum
  intro S hS
  induction labeledWickPairings S with
  | nil => simpa only [List.map_nil,List.sum_nil] using hasDerivAt_const r (0 : ℝ)
  | cons L T ih =>
    simp only [List.map_cons,List.sum_cons]
    have h := ((radialWickMonomial_hasDerivAt (Finset.univ\S).card L.length r).const_mul
      (latitudeEvenWickCoefficient n L.length)).mul_const (latitudePairingContraction n p J u S L)
    rw [←(radialWickMonomial_hasDerivAt (Finset.univ\S).card L.length r).deriv] at h
    exact h.add ih

/-- Actual physical mean splits with all higher Gaussian contractions retained. -/
theorem actual_orderedHamiltonian_latitude_mean_eq_leading_add_correction {n : ℕ} (hn : 1≤n) (p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    (∫ v : Vector (n+1),Hamiltonian (n+1) p J v
      ∂SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r)=
      r^p*Hamiltonian (n+1) p J u+pairedLatitudeCorrection n p J u r := by
  rw [actual_orderedHamiltonian_latitude_mean_eq_pairedPolynomial hn p J u hu hr,
    pairedLatitudePolynomial_eq_leading_add_correction]

/-- Every true nonempty Wick correction contains at least one pair. -/
theorem nonempty_Wick_pairing_length_pos {p : ℕ} {S : Finset (Fin p)} (hS : S≠∅)
    {L : List (Fin p×Fin p)} (hL : L∈labeledWickPairings S) : 0<L.length := by
  have hc := labeledWickPairings_card S L hL
  have hcard : 0<S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  omega

end
end SlowEquilibration.SphericalLatitudeTensorMoments
