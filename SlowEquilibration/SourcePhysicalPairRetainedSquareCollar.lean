-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereCriticalCollar
public import SlowEquilibration.SphericalFiniteCountDecomposition
public import SlowEquilibration.SourcePhysicalPairSelectionEvent
public import SlowEquilibration.SphericalMarkedMaximumEvents

/-! The literal selected critical points have no positive-overlap neighbors
outside the central pair window.  This applies the actual sphere geodesic
collar and the all-point band condition before the finite simplex count. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows SphericalMorse
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Once the regularity constant and pair-intensity cutoff are chosen from
a common fixed mark box, the band and separation widths can be selected in
the manuscript order.  This does not choose either upstream constant. -/
theorem source_pair_cutoff_collar_parameters {κ C cut : ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (hcut : 0 < cut) :
    ∃ η ε : ℝ, 0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss κ C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η := by
  obtain ⟨hLoss,_,_⟩ := sourceCriticalCollar_parameters hκ hC
  let η := min (sourceCriticalCollarOverlapLoss κ C / 2) (1/4 : ℝ)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηLoss : η ≤ sourceCriticalCollarOverlapLoss κ C :=
    (min_le_left _ _).trans (by linarith)
  have hηOne : η < 1 := by dsimp [η]; linarith [min_le_right (sourceCriticalCollarOverlapLoss κ C / 2) (1/4 : ℝ)]
  let ε := min (cut^2/4) ((1-η)/2)
  have hε : 0 < ε := lt_min
    (div_pos (sq_pos_of_pos hcut) (by norm_num))
    (div_pos (sub_pos.mpr hηOne) (by norm_num))
  refine ⟨η,ε,hη,hηLoss,hε,?_,?_⟩
  · have H := min_le_left (cut^2/4) ((1-η)/2)
    have hc : 0 < cut^2 := sq_pos_of_pos hcut
    dsimp [ε]
    linarith
  · have H := min_le_right (cut^2/4) ((1-η)/2)
    dsimp [ε]
    linarith

/-- All points in the actual selected critical family obey the printed
small upper overlap, including a pair arbitrarily near coincidence.  The
window height is a condition on the actual field, not a pair-count axiom. -/
theorem source_selected_critical_family_upper_overlap {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hδ : δ < G/2)
    (s : Finset (Vector (n+1)))
    (hsphere : ∀ u ∈ s, ‖u‖^2=(n+1:ℕ))
    (hcritical : ∀ u ∈ s, surfaceGradient (field c J) u=0)
    (hselected : ∀ u ∈ s, sourceSelectionEvent c κ C ε η E G J u)
    (hheight : ∀ u ∈ s, (n+1:ℕ)*(E-δ) ≤ field c J u) :
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → overlap u v ≤ ε := by
  intro u hu v hv huv
  exact (sourceSelectionEvent_excludes_high_critical_points c J hκ hC hη hδ
    u v (hsphere u hu) (hsphere v hv) huv (hcritical u hu) (hcritical v hv)
      (hselected u hu) (hheight v hv)).le

/-- Deterministic source 11.13 square-count split for the actual selected
critical family.  The central term counts genuine ordered point pairs; the
linear constant is exactly the simplex constant and includes antipodals. -/
theorem source_selected_critical_family_square_bound {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hδG : δ < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2)
    (s : Finset (Vector (n+1)))
    (hsphere : ∀ u ∈ s, ‖u‖^2=(n+1:ℕ))
    (hcritical : ∀ u ∈ s, surfaceGradient (field c J) u=0)
    (hselected : ∀ u ∈ s, sourceSelectionEvent c κ C ε η E G J u)
    (hheight : ∀ u ∈ s, (n+1:ℕ)*(E-δ) ≤ field c J u) :
    (s.card:ℝ)^2 ≤
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ))+
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  have hpair : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → overlap u v ≤ ε :=
    source_selected_critical_family_upper_overlap c J hκ hC hη hδG
      s hsphere hcritical hselected hheight
  have H := spherical_square_count_le_central_pairs_add (N:=n+1)
    (ι:=Vector (n+1)) (v:=id) (by omega) s hδ hδOne hε hsphere hpair
  simpa only [id_eq] using H

/-- The lower energy assumption above follows directly from the original
normalized score window.  Thus the same square split applies to the true
selected physical mark window, with no supplied field-height predicate. -/
theorem source_selected_score_window_square_bound {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hδG : δ < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hwindow : ∀ z ∈ K, E-δ ≤ z 0)
    (s : Finset (Vector (n+1)))
    (hsphere : ∀ u ∈ s, ‖u‖^2=(n+1:ℕ))
    (hcritical : ∀ u ∈ s, surfaceGradient (field c J) u=0)
    (hselected : ∀ u ∈ s, sourceSelectionEvent c κ C ε η E G J u)
    (hmark : ∀ u ∈ s, actualScore c J u ∈ K) :
    (s.card:ℝ)^2 ≤
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ))+
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  have hheight : ∀ u ∈ s, (n+1:ℕ)*(E-δ) ≤ field c J u := by
    intro u hu
    have hscore := hwindow (actualScore c J u) (hmark u hu)
    rw [actualScore_value_eq] at hscore
    have hN : (0:ℝ) < (n+1:ℕ) := by positivity
    have H := mul_le_mul_of_nonneg_left hscore hN.le
    exact H.trans_eq (by field_simp [ne_of_gt hN])
  exact source_selected_critical_family_square_bound c J hκ hC hη hδG
    hδ hδOne hε s hsphere hcritical hselected hheight

/-- The exact selected subset of the actual sphere critical set. -/
def sourceSelectedScoreWindowSet {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (κ C ε η E G : ℝ) : Set (Vector (n+1)) :=
  {u | u ∈ sphereCriticalSet n c J ∧ actualScore c J u ∈ K ∧
    sourceSelectionEvent c κ C ε η E G J u}

theorem sourceSelectedScoreWindowSet_finite {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (κ C ε η E G : ℝ) (hfinite : (sphereCriticalSet n c J).Finite) :
    (sourceSelectedScoreWindowSet c J K κ C ε η E G).Finite := by
  apply hfinite.subset
  intro u hu
  exact hu.1

theorem sourceSelectedScoreWindowSet_finite_ae (n : ℕ) (hn : 1 ≤ n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      (sourceSelectedScoreWindowSet c J K κ C ε η E G).Finite := by
  dsimp only
  filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
  exact sourceSelectedScoreWindowSet_finite _ J K κ C ε η E G hfinite

/-- The finite selected set itself satisfies the source 11.13
decomposition, so no arbitrary finite-family hypothesis remains. -/
theorem source_actual_selected_score_window_square_bound {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G δ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hδG : δ < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hwindow : ∀ z ∈ K, E-δ ≤ z 0)
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
  apply source_selected_score_window_square_bound c J hκ hC hη hδG hδ hδOne hε K hwindow s
  · intro u hu
    exact (hm u hu).1.1
  · intro u hu
    exact (hm u hu).1.2
  · intro u hu
    exact (hm u hu).2.2
  · intro u hu
    exact (hm u hu).2.1

end
end SlowEquilibration.PairConditionalDeterminantMoments
