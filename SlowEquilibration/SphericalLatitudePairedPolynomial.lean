-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteWickPairingOrder
public import SlowEquilibration.SphericalLatitudeWickRadialPolynomial

/-! Actual finite latitude mean expanded into literal original coefficient
pair contractions and the exact radial polynomials. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel FiniteWickPairings
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sum_list_finset_swap {ι κ : Type*} (s : Finset ι) (L : List κ) (f : ι→κ→ℝ) :
    (∑ i∈s,(L.map (f i)).sum)=(L.map (fun k => ∑ i∈s,f i k)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

/-- Literal coefficient pairing; every entry remains an original ordered tensor coordinate. -/
def latitudePairingContraction (n p : ℕ) (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (u : Vector (n+1)) (S : Finset (Fin p)) (L : List (Fin p×Fin p)) : ℝ :=
  normalization (n+1) p*∑ I : TensorIndex (n+1) p,J I*
    (∏ k∈Finset.univ\S,u (I k))*pairingWeight (latitudeProjectionCovariance u I) L

def pairedLatitudePolynomial (n p : ℕ) (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (u : Vector (n+1)) (r : ℝ) : ℝ :=
  ∑ S∈(Finset.univ : Finset (Fin p)).powerset,
    ((labeledWickPairings S).map (fun L => latitudeEvenWickCoefficient n L.length*
      radialWickMonomial (Finset.univ\S).card L.length r*latitudePairingContraction n p J u S L)).sum

/-- Actual labeled contractions have the genuine even radial factor, with
physical Gaussian-radius coefficient retained. -/
theorem actual_latitude_pairing_factor {n : ℕ} (hn : 1≤n) {p : ℕ}
    (u : Vector (n+1)) {r : ℝ} (hr : |r|≤1) (S : Finset (Fin p))
    (L : List (Fin p×Fin p)) (hL : L∈labeledWickPairings S) (I : TensorIndex (n+1) p) :
    (∏ k∈Finset.univ\S,r*u (I k))*latitudeWickCoefficient n r S.card*
        pairingWeight (latitudeProjectionCovariance u I) L=
      latitudeEvenWickCoefficient n L.length*radialWickMonomial (Finset.univ\S).card L.length r*
        ((∏ k∈Finset.univ\S,u (I k))*pairingWeight (latitudeProjectionCovariance u I) L) := by
  rw [←labeledWickPairings_card S L hL,latitudeWickCoefficient_even_eq hn hr]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,radialWickMonomial]
  ring

/-- Literal Hamiltonian latitude mean is this finite physical paired polynomial. -/
theorem actual_orderedHamiltonian_latitude_mean_eq_pairedPolynomial {n : ℕ} (hn : 1≤n) (p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r|≤1) :
    (∫ v : Vector (n+1),Hamiltonian (n+1) p J v
      ∂SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r)=
      pairedLatitudePolynomial n p J u r := by
  rw [actual_orderedHamiltonian_latitude_mean hn p J u hu hr]
  unfold orderedLatitudeWickMoment pairedLatitudePolynomial
  simp_rw [covarianceWickSum_eq_pairings,Finset.mul_sum,←List.sum_map_mul_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [sum_list_finset_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro L hL
  rw [latitudePairingContraction]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←mul_assoc]
  have hf := actual_latitude_pairing_factor hn u hr S L hL I
  dsimp only [radialWickMonomial] at hf
  dsimp only [radialWickMonomial]
  linear_combination (normalization (n+1) p*J I)*hf

/-- All radial dependence is a genuine finite polynomial before conditioning. -/
theorem pairedLatitudePolynomial_hasDerivAt (n p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1)) (r : ℝ) :
    HasDerivAt (pairedLatitudePolynomial n p J u)
      (∑ S∈(Finset.univ : Finset (Fin p)).powerset,
        ((labeledWickPairings S).map (fun L => latitudeEvenWickCoefficient n L.length*
          deriv (radialWickMonomial (Finset.univ\S).card L.length) r*
            latitudePairingContraction n p J u S L)).sum) r := by
  unfold pairedLatitudePolynomial
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

end
end SlowEquilibration.SphericalLatitudeTensorMoments
