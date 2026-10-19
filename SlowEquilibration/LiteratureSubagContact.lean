-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagPhysicalDefinitions

@[expose] public section

/-!
# Subag's contact-to-multisamplability implication

Theorem 10, forward implication (1.39), of Subag,
*Free energy landscapes in spherical spin glasses*, Duke Math. J. 173 (2024),
arXiv:1804.10576v6, applies to every admissible spherical mixture.  Only
the converse (1.40) in that theorem needs genericity.  Its premise and
conclusion are explicit theorem arguments below.  The actual source
certificate is then proved to give the paper's contact condition.
-/

namespace SlowEquilibration.LiteratureSubagContact

noncomputable section
open Set CrisantiSommers CSParisiMeasure
open SphericalTAPCertificate
open LiteratureSubagPhysicalDefinitions
set_option autoImplicit false

/-- The forward direction of published Theorem 10, stated for the
repository's canonical CS first variation and original annealed Gibbs
replicas.  This is an explicit external theorem hypothesis, not an axiom. -/
def Theorem10Forward (μ : FiniteMixture) (β : ℝ) : Prop :=
  0 < β ∧ ∀ q : ℝ, Contact μ β q → MultiSamplable μ β q

/-- A literal strict one-step certificate supplies a contact of the
canonical minimizer in precisely Subag's optimality set. -/
theorem certificate_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) : Contact μ β Q := by
  have hQzero : firstVariation β μ.xi (canonicalMinimizer μ β).law Q = 0 := by
    rw [h.canonical_law]
    have hv : -firstVariation β μ.xi (twoAtom x Q) Q = 0 := h.contact_value
    exact neg_eq_zero.mp hv
  have hmax := (CSStructure.minimizer_firstVariation_maximum_zero
    μ (le_trans (by norm_num : 3 ≤ 4) h.min_degree) h.beta_pos
    (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β)).1
  exact ⟨⟨h.overlap_range.1.le,h.overlap_range.2⟩,
    fun r hr => by simpa only [hQzero] using hmax r hr⟩

/-- The cited forward implication applies at the actual contact `Q` of
every source certificate, including a one-degree pure model of either parity. -/
theorem certificate_multiSamplable (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (h10 : Theorem10Forward μ β) :
    MultiSamplable μ β Q :=
  h10.2 Q (certificate_contact μ h)

end
end SlowEquilibration.LiteratureSubagContact
