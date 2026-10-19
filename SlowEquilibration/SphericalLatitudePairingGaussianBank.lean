-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteWickPairingSlots
public import SlowEquilibration.SphericalLatitudePairedPolynomial
public import SlowEquilibration.PairedTensorProjectionOriginalLaw

/-! Every true finite Wick pairing extracts its projected tensor from the
actual original iid coefficient bank. No conditional mean, coefficient law,
or uniform-envelope conclusion is supplied as a premise. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalAging.FiniteModel (TensorIndex normalization)
open SphericalModel (Vector)
open FiniteWickPairings PairedTensorProjectionFeatures SphericalProjectionMatrixFeature
open PureTensorJetBounds
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairingTensorIndexEquiv {N p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) :
    TensorIndex N p≃TensorIndex N ((Finset.univ\S).card+L.length+L.length) :=
  Equiv.arrowCongr (pairingBlockEquiv S L hL).symm (Equiv.refl (Fin N))

theorem pairingTensorIndexEquiv_apply {N p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) (I : TensorIndex N p) :
    pairingTensorIndexEquiv (N := N) S L hL I=I ∘ pairingBlockEquiv S L hL := rfl

def pairingReindexedTensor {N p : ℕ} (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) :
    SphericalAging.FiniteModel.Disorder N p≃ᵐ
      SphericalAging.FiniteModel.Disorder N ((Finset.univ\S).card+L.length+L.length) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : TensorIndex N ((Finset.univ\S).card+L.length+L.length) => ℝ)
    (pairingTensorIndexEquiv S L hL)

theorem pairingReindexedTensor_apply_image {N p : ℕ} (S : Finset (Fin p))
    (L : List (Fin p×Fin p)) (hL : ValidPairing S L)
    (J : SphericalAging.FiniteModel.Disorder N p) (I : TensorIndex N p) :
    pairingReindexedTensor S L hL J (pairingTensorIndexEquiv S L hL I)=J I := by
  change Equiv.piCongrLeft
    (fun _ : TensorIndex N ((Finset.univ\S).card+L.length+L.length) => ℝ)
    (pairingTensorIndexEquiv S L hL) J
    (pairingTensorIndexEquiv S L hL I)=J I
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant,Equiv.symm_apply_apply]

/-- Literal row reindexing preserves the true original ordered iid tensor law. -/
theorem pairingReindexedTensor_measurePreserving {N p : ℕ} (S : Finset (Fin p))
    (L : List (Fin p×Fin p)) (hL : ValidPairing S L) :
    MeasurePreserving (pairingReindexedTensor (N := N) S L hL)
      (SphericalAging.FiniteModel.disorderLaw N p)
      (SphericalAging.FiniteModel.disorderLaw N ((Finset.univ\S).card+L.length+L.length)) :=
  measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) (pairingTensorIndexEquiv S L hL)

/-- Exact normalized physical original pairing contraction, including every Π_u entry. -/
theorem latitudePairingContraction_div_sqrt_eq_originalProjectedTrace {n p : ℕ}
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1)) :
    latitudePairingContraction n p J u S L/Real.sqrt (n+1 : ℕ)=
      originalProjectedTrace (n+1) (Finset.univ\S).card L.length (pairingReindexedTensor S L hL J) u := by
  have hc (I : TensorIndex (n+1) p) :
      (∏ k∈Finset.univ\S,u (I k))*pairingWeight (latitudeProjectionCovariance u I) L=
        pairedTensorFeature (n+1) (Finset.univ\S).card L.length u (pairingTensorIndexEquiv S L hL I) := by
    rw [pairingTensorIndexEquiv_apply,pairedTensorFeature_pairingBlockEquiv]
    have hC : (fun a b => projectionMatrixFeature u (I a,I b))=latitudeProjectionCovariance u I := by
      funext a b
      rw [projectionMatrixFeature_apply]
      rfl
    rw [hC]
  have hi : (∑ I : TensorIndex (n+1) p,J I*
      (∏ k∈Finset.univ\S,u (I k))*pairingWeight (latitudeProjectionCovariance u I) L)=
      inner ℝ (pairedTensorFeature (n+1) (Finset.univ\S).card L.length u)
        (WithLp.toLp 2 (pairingReindexedTensor S L hL J)) := by
    change _=∑ I,pairingReindexedTensor S L hL J I*
      pairedTensorFeature (n+1) (Finset.univ\S).card L.length u I
    calc
      _=∑ I : TensorIndex (n+1) p,pairingReindexedTensor S L hL J (pairingTensorIndexEquiv S L hL I)*
          pairedTensorFeature (n+1) (Finset.univ\S).card L.length u (pairingTensorIndexEquiv S L hL I) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [pairingReindexedTensor_apply_image,mul_assoc,hc]
      _=_ := Equiv.sum_comp (pairingTensorIndexEquiv S L hL)
        (fun I => pairingReindexedTensor S L hL J I*
          pairedTensorFeature (n+1) (Finset.univ\S).card L.length u I)
  have hnorm : normalization (n+1) p=
      normalization (n+1) ((Finset.univ\S).card+L.length+L.length) :=
    congrArg (normalization (n+1)) (valid_pairing_degree hL).symm
  rw [latitudePairingContraction,hi,originalProjectedTrace,hnorm]
  ring

def latitudePairingEnvelope (n p : ℕ) (S : Finset (Fin p)) (L : List (Fin p×Fin p))
    (hL : ValidPairing S L) (J : SphericalAging.FiniteModel.Disorder (n+1) p) : ℝ :=
  originalPairedEnvelope (n+1) (Finset.univ\S).card L.length (pairingReindexedTensor S L hL J)

theorem latitudePairingContraction_abs_le_envelope {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : UnitSphere (n+1)) :
    |latitudePairingContraction n p J (physicalAxis u) S L/Real.sqrt (n+1 : ℕ)|≤
      latitudePairingEnvelope n p S L hL J := by
  rw [latitudePairingContraction_div_sqrt_eq_originalProjectedTrace]
  exact originalProjectedTrace_abs_le_envelope (by omega) (Finset.univ\S).card L.length _ u

/-- The same genuine envelope controls every physical conditioning axis. -/
theorem latitudePairingContraction_abs_le_envelope_onSphere {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
    |latitudePairingContraction n p J u S L/Real.sqrt (n+1 : ℕ)|≤latitudePairingEnvelope n p S L hL J := by
  obtain ⟨v,hv⟩ := exists_unit_scale (by omega) u
  rw [SphericalAging.LandscapeDerivatives.sphere_norm u hu] at hv
  rw [hv]
  exact latitudePairingContraction_abs_le_envelope hn S L hL J v

theorem latitudePairingEnvelope_integrable {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L) :
    Integrable (latitudePairingEnvelope n p S L hL) (SphericalAging.FiniteModel.disorderLaw (n+1) p) :=
  (pairingReindexedTensor_measurePreserving S L hL).hasLaw.integrable_comp
    (originalPairedEnvelope_integrable (N := n+1) (by omega) (Finset.univ\S).card L.length)

/-- True expected normalized contraction scale for every higher Wick correction. -/
theorem expected_latitudePairingEnvelope_le {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L) (hj : 0 < L.length) :
    (∫ J,latitudePairingEnvelope n p S L hL J ∂SphericalAging.FiniteModel.disorderLaw (n+1) p)≤
      2*Real.sqrt ((Finset.univ\S).card+4*(L.length : ℝ))*
        ((n+1 : ℕ) : ℝ)^((1-(L.length : ℝ))/2) := by
  have h := (pairingReindexedTensor_measurePreserving (N := n+1) S L hL).hasLaw.integral_comp
    (originalPairedEnvelope_integrable (N := n+1) (by omega) (Finset.univ\S).card L.length).aestronglyMeasurable
  change (∫ J,latitudePairingEnvelope n p S L hL J ∂_)=(∫ J,originalPairedEnvelope (n+1) (Finset.univ\S).card L.length J ∂_) at h
  rw [h]
  exact expected_originalPairedEnvelope_le (by omega) (Finset.univ\S).card L.length hj

/-- Genuine original-disorder failure event for each actual Wick correction. -/
theorem latitudePairingEnvelope_upper_tail {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L) (hj : 0 < L.length)
    {s : ℝ} (hs : 0 ≤ s) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p
      {J | 2*Real.sqrt ((Finset.univ\S).card+4*(L.length : ℝ))+s≤latitudePairingEnvelope n p S L hL J}≤
      ENNReal.ofReal (2*Real.exp (-s^2*((n+1 : ℕ) : ℝ)/2)) := by
  have h := originalPairedEnvelope_upper_tail (show 2≤n+1 by omega) (Finset.univ\S).card L.length hj hs
  have hc : Continuous (originalPairedEnvelope (n+1) (Finset.univ\S).card L.length) :=
    (pairedGaussianEnvelope_lipschitz (by omega) (Finset.univ\S).card L.length hj).continuous.comp (by fun_prop)
  have hm : MeasurableSet {J : SphericalAging.FiniteModel.Disorder (n+1) ((Finset.univ\S).card+L.length+L.length) |
      2*Real.sqrt ((Finset.univ\S).card+4*(L.length : ℝ))+s≤originalPairedEnvelope (n+1) (Finset.univ\S).card L.length J} :=
    (isClosed_le continuous_const hc).measurableSet
  nth_rw 1 [←(pairingReindexedTensor_measurePreserving S L hL).map_eq] at h
  rw [Measure.map_apply (pairingReindexedTensor S L hL).measurable hm] at h
  exact h

end
end SlowEquilibration.SphericalLatitudeTensorMoments
