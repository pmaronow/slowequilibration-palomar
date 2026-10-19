-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedSquareCollar

/-! Separate the energy-band width from the overlap cutoff in the actual
sphere square count.  The manuscript fixes its local pair cutoff before ε;
the small energy band is chosen later from the positive gap Gε. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows SphericalMorse
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_selected_critical_family_square_bound_decoupled {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G ω δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2)
    (s : Finset (Vector (n+1)))
    (hsphere : ∀ u ∈ s, ‖u‖^2=(n+1:ℕ))
    (hcritical : ∀ u ∈ s, surfaceGradient (field c J) u=0)
    (hselected : ∀ u ∈ s, sourceSelectionEvent c κ C ε η E G J u)
    (hheight : ∀ u ∈ s, (n+1:ℕ)*(E-ω) ≤ field c J u) :
    (s.card:ℝ)^2 ≤
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ))+
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  have hUpper : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → overlap u v ≤ ε :=
    source_selected_critical_family_upper_overlap c J hκ hC hη hωG
      s hsphere hcritical hselected hheight
  have H := spherical_square_count_le_central_pairs_add (N:=n+1)
    (ι:=Vector (n+1)) (v:=id) (by omega) s hδ hδOne hε hsphere hUpper
  simpa only [id_eq] using H

theorem source_actual_selected_score_window_square_bound_decoupled {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G ω δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    let s := (sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite).toFinset
    (s.card:ℝ)^2 ≤
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ))+
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  let hs := sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite
  let s := hs.toFinset
  have hm : ∀ u ∈ s, u ∈ sourceSelectedScoreWindowSet c J K κ C ε η E G := by
    intro u hu
    exact (Set.Finite.mem_toFinset hs).mp hu
  apply source_selected_critical_family_square_bound_decoupled c J hκ hC hη hωG
    hδ hδOne hε s
  · intro u hu
    exact (hm u hu).1.1
  · intro u hu
    exact (hm u hu).1.2
  · intro u hu
    exact (hm u hu).2.2
  · intro u hu
    have hscore := hwindow (actualScore c J u) (hm u hu).2.1
    rw [actualScore_value_eq] at hscore
    have hN : (0:ℝ) < (n+1:ℕ) := by positivity
    have H := mul_le_mul_of_nonneg_left hscore hN.le
    exact H.trans_eq (by field_simp [ne_of_gt hN])

end
end SlowEquilibration.PairConditionalDeterminantMoments
