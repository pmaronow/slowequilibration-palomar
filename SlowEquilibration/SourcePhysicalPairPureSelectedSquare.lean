-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairDecoupledSquareCollar
public import SlowEquilibration.SourcePhysicalPurePairRetainedPairDefinitions

/-! The actual pure value-window retained count as a finite selected set,
with an energy-band width independent of the pair overlap cutoff. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse SphericalForm
open SphericalPairMarkedWindows
open scoped ENNReal RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

def sourceSelectedValueWindowSet {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (I : Set ℝ)
    (κ C ε η E G : ℝ) : Set (Vector (n+1)) :=
  {u | u ∈ sphereCriticalSet n c J ∧ actualValue c J u ∈ I ∧
    sourceSelectionEvent c κ C ε η E G J u}

theorem sourceSelectedValueWindowSet_finite {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (I : Set ℝ) (κ C ε η E G : ℝ)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    (sourceSelectedValueWindowSet c J I κ C ε η E G).Finite := by
  apply hfinite.subset
  intro u hu
  exact hu.1

theorem sourceRetainedValueWindowCount_eq_selected_set_card {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (I : Set ℝ) (κ C ε η E G : ℝ)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    sourceRetainedValueWindowCount n c I κ C ε η E G J =
      (((sourceSelectedValueWindowSet_finite c J I κ C ε η E G
        hfinite).toFinset.card):ℝ≥0∞) := by
  classical
  let A : Set (Vector (n+1)) :=
    {u | ‖u‖^2=(n+1:ℕ) ∧ surfaceGradient (field c J) u=0 ∧
      actualValue c J u∈I}
  let B : Set (Vector (n+1)) :=
    sourceSelectedValueWindowSet c J I κ C ε η E G
  have hA : A.Finite := by
    apply hfinite.subset
    intro u hu
    exact ⟨hu.1,hu.2.1⟩
  let hB : B.Finite := sourceSelectedValueWindowSet_finite c J I κ C ε η E G hfinite
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
  unfold sourceRetainedValueWindowCount actualValueWindowCount
  change (∑' u : A, sourceSelectionMark c κ C ε η E G J u) = _
  rw [tsum_fintype]
  have hbool : (∑ u : A, sourceSelectionMark c κ C ε η E G J u) =
      (((Finset.univ.filter Psel).card):ℝ≥0∞) := by
    simpa only [sourceSelectionMark,Psel] using
      Finset.sum_boole (R:=ℝ≥0∞) Psel (Finset.univ)
  rw [hbool]
  exact congrArg (fun k : ℕ => (k:ℝ≥0∞)) hcard

theorem source_actual_selected_value_window_square_bound {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G ω cut : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hcut : 0 < cut) (hcutOne : cut ≤ 1) (hε : ε < cut^2)
    (I : Set ℝ) (hwindow : ∀ z ∈ I, E-ω ≤ z)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    let s := (sourceSelectedValueWindowSet_finite c J I κ C ε η E G
      hfinite).toFinset
    (s.card:ℝ)^2 ≤
      (∑ u ∈ s,
        ((s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card:ℝ))+
      (1+(1-ε)/(cut^2-ε))*(s.card:ℝ) := by
  let hs := sourceSelectedValueWindowSet_finite c J I κ C ε η E G hfinite
  let s := hs.toFinset
  have hm : ∀ u ∈ s, u ∈ sourceSelectedValueWindowSet c J I κ C ε η E G := by
    intro u hu
    exact (Set.Finite.mem_toFinset hs).mp hu
  apply source_selected_critical_family_square_bound_decoupled c J hκ hC hη hωG
    hcut hcutOne hε s
  · intro u hu
    exact (hm u hu).1.1
  · intro u hu
    exact (hm u hu).1.2
  · intro u hu
    exact (hm u hu).2.2
  · intro u hu
    have hvalue := hwindow (actualValue c J u) (hm u hu).2.1
    unfold actualValue at hvalue
    have hN : (0:ℝ) < (n+1:ℕ) := by positivity
    have H := mul_le_mul_of_nonneg_left hvalue hN.le
    exact H.trans_eq (by field_simp [ne_of_gt hN])

end
end SlowEquilibration.PairConditionalDeterminantMoments
