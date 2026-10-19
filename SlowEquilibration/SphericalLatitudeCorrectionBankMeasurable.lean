-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCorrectionEnvelopeTail

/-! The genuine finite original Gaussian-bank event is Borel, allowing
its exact per-degree product-law transport in the mixed model. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set FiniteWickPairings PairedTensorProjectionFeatures
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual projected-bank envelope is continuous for every higher pair. -/
theorem latitudePairingEnvelope_continuous {n p : ℕ} (hn : 1≤n)
    (S : Finset (Fin p)) (L : List (Fin p×Fin p)) (hL : ValidPairing S L) (hj : 0<L.length) :
    Continuous (latitudePairingEnvelope n p S L hL) := by
  unfold latitudePairingEnvelope originalPairedEnvelope
  apply (pairedGaussianEnvelope_lipschitz (by omega) (Finset.univ\S).card L.length hj).continuous.comp
  have he : (fun J : SphericalAging.FiniteModel.Disorder (n+1) p =>
      WithLp.toLp 2 (pairingReindexedTensor S L hL J))=
      fun J => WithLp.toLp 2 (fun I => J ((pairingTensorIndexEquiv S L hL).symm I)) := by
    funext J
    apply PiLp.ext
    intro I
    have h := pairingReindexedTensor_apply_image S L hL J ((pairingTensorIndexEquiv S L hL).symm I)
    simpa only [Equiv.apply_symm_apply] using h
  rw [he]
  fun_prop

/-- Genuine finite bad-bank union is Borel in the original raw tensor. -/
theorem latitudeCorrectionBadBanks_measurable {n p : ℕ} (hn : 1≤n) :
    MeasurableSet (latitudeCorrectionBadBanks n p) := by
  unfold latitudeCorrectionBadBanks
  apply MeasurableSet.iUnion
  intro S
  apply MeasurableSet.iUnion
  intro hS
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro L
  simp only [List.mem_attach,true_and]
  have hj := nonempty_Wick_pairing_length_pos (Finset.mem_erase.mp hS).1 L.property
  exact (isClosed_le continuous_const (latitudePairingEnvelope_continuous hn S L.val
    (labeledWickPairings_valid S L.val L.property) hj)).measurableSet

end
end SlowEquilibration.SphericalLatitudeTensorMoments
