-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCenter

/-! A total deterministic indexing of the unique pure local-maximum
tail center; exceptional early dimensions use the contact-energy fallback. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology

theorem sourcePure_truncatedLocalMax_center_sequence
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M : ℝ, 0 < M ∧
      (∀ n < n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n ≥ n₀,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n)=1 ∧
        (∀ y : ℝ, tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) := by
  classical
  obtain ⟨M,hM,hEvent⟩ := sourcePure_truncatedLocalMax_normalized_center
    p hp a ha h hm hg hLeft hRight
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hEvent
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let m : ℕ → ℝ := fun n => if hn : n₀ ≤ n then Classical.choose (hn₀ n hn)
    else (n+2 : ℕ)*E
  refine ⟨n₀,m,M,hM,?_,?_⟩
  · intro n hn
    simp only [m,dite_eq_right (not_le.mpr hn),E]
  · intro n hn
    simpa only [m,dite_eq_left hn] using Classical.choose_spec (hn₀ n hn)

end SlowEquilibration.SphericalMarkedWindows
