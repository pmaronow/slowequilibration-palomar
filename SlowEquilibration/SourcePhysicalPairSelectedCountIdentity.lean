-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedSquareCollar

/-! Identify the literal retained score-window count with the ordinary
cardinality of its actual finite set of selected sphere critical points. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem sourceRetainedScoreWindowCount_eq_selected_set_card {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G : ℝ)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    sourceRetainedScoreWindowCount n c K κ C ε η E G J =
      (((sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite).toFinset.card):ℝ≥0∞) := by
  classical
  let A : Set (Vector (n+1)) :=
    {u | ‖u‖^2=(n+1:ℕ) ∧ surfaceGradient (field c J) u=0 ∧ actualScore c J u∈K}
  let B : Set (Vector (n+1)) := sourceSelectedScoreWindowSet c J K κ C ε η E G
  have hA : A.Finite := by
    apply hfinite.subset
    intro u hu
    exact ⟨hu.1,hu.2.1⟩
  let hB : B.Finite := sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite
  have instA : Fintype A := hA.fintype
  have instB : Fintype B := hB.fintype
  let Psel : A → Prop := fun u => sourceSelectionEvent c κ C ε η E G J u
  let e : B ≃ {u : A // Psel u} := {
    toFun := fun u => ⟨⟨u.val,⟨u.property.1.1,u.property.1.2,u.property.2.1⟩⟩,
      u.property.2.2⟩
    invFun := fun u => ⟨u.val.val,
      ⟨⟨u.val.property.1,u.val.property.2.1⟩,u.val.property.2.2,u.property⟩⟩
    left_inv := by intro u; apply Subtype.ext; rfl
    right_inv := by intro u; apply Subtype.ext; apply Subtype.ext; rfl }
  have hcard : (Finset.univ.filter Psel).card = hB.toFinset.card := by
    calc
      (Finset.univ.filter Psel).card = Fintype.card {u : A // Psel u} :=
        (Fintype.card_subtype Psel).symm
      _ = Fintype.card B := Fintype.card_congr e.symm
      _ = hB.toFinset.card := (Set.Finite.card_toFinset hB).symm
  unfold sourceRetainedScoreWindowCount actualScoreWindowCount
  change (∑' u : A, sourceSelectionMark c κ C ε η E G J u) = _
  rw [tsum_fintype]
  have hbool : (∑ u : A, sourceSelectionMark c κ C ε η E G J u) =
      (((Finset.univ.filter Psel).card):ℝ≥0∞) := by
    simpa only [sourceSelectionMark,Psel] using
      Finset.sum_boole (R:=ℝ≥0∞) Psel (Finset.univ)
  rw [hbool]
  exact congrArg (fun k : ℕ => (k:ℝ≥0∞)) hcard

end
end SlowEquilibration.PairConditionalDeterminantMoments
