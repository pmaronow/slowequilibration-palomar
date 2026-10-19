-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalStoppedSolutionUniqueness

/-! Two canonical spherical C¹ diffusions driven by the same Wiener path
agree until exiting any open region on which their ambient gradients agree. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalC1LocalAgreement
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
open SphericalAging HardSphereDynamics LocalSDE ClosedHitStopping CutoffSphere
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalDynamics
open SlowEquilibration.SphericalC1Dynamics
open SlowEquilibration.SphericalStoppedSolutionUniqueness
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {N : ℕ}

theorem c1Process_agree_before_open_exit
    (hN : N ≠ 0) (β : ℝ)
    (g g' : State N → State N)
    (hg : ContDiff ℝ 1 g) (hg' : ContDiff ℝ 1 g')
    (z : State N → ℝ) (hz : Continuous z)
    (hgrad : ∀ y, z y < 1 → g y = g' y)
    (x : State N) (hx : OnSphere x) (hxz : z x < 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, t ≤ T →
      (∀ s, s < t → z (process β g hg x s ω) < 1) →
      process β g hg x t ω = process β g' hg' x t ω := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let R := cutoffRadius N
  let hR := cutoffRadius_pos N
  let Kb := (cutoffDrift_lipschitz β g hg R hR).choose
  let Kc := (cutoffDrift_lipschitz β g' hg' R hR).choose
  let Ks := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose
  let bg := (cutoffDrift_lipschitz β g hg R hR).choose_spec
  let bg' := (cutoffDrift_lipschitz β g' hg' R hR).choose_spec
  let bs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  let X₀ := process β g hg x
  let Y₀ := process β g' hg' x
  have hX₀a : StronglyAdapted F X₀ :=
    GlobalSDE.process_stronglyAdapted D bg bs x
  have hY₀a : StronglyAdapted F Y₀ :=
    GlobalSDE.process_stronglyAdapted D bg' bs x
  have hX₀c : ∀ᵐ ω ∂P, Continuous (fun t => X₀ t ω) :=
    process_continuous β g hg x
  have hY₀c : ∀ᵐ ω ∂P, Continuous (fun t => Y₀ t ω) :=
    process_continuous β g' hg' x
  obtain ⟨X,hXa,hXc,hXX₀⟩ :=
    NullAugmentation.exists_allPath_continuous_modification_augmented
      (VectorBrownian.filtration N) X₀ hX₀a hX₀c
  obtain ⟨Y,hYa,hYc,hYY₀⟩ :=
    NullAugmentation.exists_allPath_continuous_modification_augmented
      (VectorBrownian.filtration N) Y₀ hY₀a hY₀c
  have hXsol : IsLocalStrongSolutionOn (cutoffDrift β g R hR)
      (CutoffSDE.cutoffNoise N R hR) (fun i j => (bs i j).continuous) D x X T :=
    AllPathSDE.IsLocalStrongSolutionOn.path_congr
      (GlobalSDE.process_strongSolution D bg bs x T) hXa (.of_forall hXc) hXX₀
  have hYsol : IsLocalStrongSolutionOn (cutoffDrift β g' R hR)
      (CutoffSDE.cutoffNoise N R hR) (fun i j => (bs i j).continuous) D x Y T :=
    AllPathSDE.IsLocalStrongSolutionOn.path_congr
      (GlobalSDE.process_strongSolution D bg' bs x T) hYa (.of_forall hYc) hYY₀
  have hXs : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω) := by
    filter_upwards [hXX₀,process_onSphere hN β g hg x hx] with ω he hs
    intro t
    rw [he t]
    exact hs t
  have hYs : ∀ᵐ ω ∂P, ∀ t, OnSphere (Y t ω) := by
    filter_upwards [hYY₀,process_onSphere hN β g' hg' x hx] with ω he hs
    intro t
    rw [he t]
    exact hs t
  have hXb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hXs] with ω hs
    intro t _
    have hsq := (onSphere_iff_norm_sq _).mp (hs t)
    nlinarith [norm_nonneg (X t ω),R.coe_nonneg,cutoffRadius_contains_sphere N]
  have hYb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖Y t ω‖ ≤ R := by
    filter_upwards [hYs] with ω hs
    intro t _
    have hsq := (onSphere_iff_norm_sq _).mp (hs t)
    nlinarith [norm_nonneg (Y t ω),R.coe_nonneg,cutoffRadius_contains_sphere N]
  let Z : ℝ≥0 → VectorBrownian.Space N → ℝ := fun t ω => z (X t ω)
  have hZc : ∀ ω, Continuous (fun t => Z t ω) := fun ω => hz.comp (hXc ω)
  have hZa : StronglyAdapted F Z := fun t => hz.comp_stronglyMeasurable (hXa t)
  let τ := firstClosedHit Z T 1
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_firstClosedHit Z hZa hZc T 1
  have hτT : ∀ ω, τ ω ≤ T := fun ω => firstClosedHit_le Z T 1 ω (hZc ω)
  have hτpos : ∀ᵐ ω ∂P, 0 < τ ω := by
    filter_upwards [hXX₀,process_zero β g hg x] with ω he hzero
    have hZzero : Z 0 ω < 1 := by
      change z (X 0 ω) < 1
      rw [(he 0).trans hzero]
      exact hxz
    by_contra hn
    have hτzero : τ ω = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have hh := (firstClosedHit_isLeast Z T 1 ω (hZc ω)).1
    change τ ω ∈ closedHitSet Z T 1 ω at hh
    rw [hτzero] at hh
    rcases hh with hlevel | hterminal
    · exact not_le_of_gt hZzero hlevel.2
    · exact (ne_of_gt hT) hterminal.symm
  have hcoef (v : State N) (hv : z v < 1) (i : Fin N) :
      cutoffDrift β g R hR i v = cutoffDrift β g' R hR i v := by
    have he : drift β g v = drift β g' v := by
      simp only [drift,hgrad v hv]
    simp only [cutoffDrift,cutoffCoefficient,he]
  have hDrift : ∀ᵐ ω ∂P, ∀ t, t ≤ τ ω → ∀ i,
      ‖cutoffDrift β g R hR i (X t ω) - cutoffDrift β g' R hR i (Y t ω)‖ ≤
        (Kc : ℝ) * ‖X t ω - Y t ω‖ := by
    filter_upwards [hτpos] with ω hpos
    intro t ht i
    let f : ℝ≥0 → ℝ := fun s =>
      ‖cutoffDrift β g R hR i (X s ω) - cutoffDrift β g' R hR i (Y s ω)‖ -
        (Kc : ℝ) * ‖X s ω - Y s ω‖
    have hf : Continuous f := by
      dsimp only [f]
      exact (((bg i).continuous.comp (hXc ω)).sub
        ((bg' i).continuous.comp (hYc ω))).norm.sub
        (continuous_const.mul ((hXc ω).sub (hYc ω)).norm)
    have hclosed : IsClosed {s : ℝ≥0 | f s ≤ 0} := isClosed_Iic.preimage hf
    have hlt : Iio (τ ω) ⊆ {s : ℝ≥0 | f s ≤ 0} := by
      intro s hs
      have hinside : z (X s ω) < 1 := below_level_before_hit Z hZc T 1 ω s hs
      have he := hcoef (X s ω) hinside i
      change ‖cutoffDrift β g R hR i (X s ω) -
        cutoffDrift β g' R hR i (Y s ω)‖ -
        (Kc : ℝ) * ‖X s ω - Y s ω‖ ≤ 0
      rw [he]
      exact sub_nonpos.mpr ((bg' i).norm_sub_le _ _)
    have hclosure : Iic (τ ω) ⊆ {s : ℝ≥0 | f s ≤ 0} := by
      have hnonempty : (Iio (τ ω)).Nonempty := ⟨0,hpos⟩
      simpa only [closure_Iio' hnonempty] using closure_minimal hlt hclosed
    exact sub_nonpos.mp (hclosure ht)
  have hsame := localStrongSolutions_unique_upTo_stop D
    (cutoffDrift β g R hR) (cutoffDrift β g' R hR)
    (CutoffSDE.cutoffNoise N R hR)
    (fun i => (bg i).continuous) (fun i => (bg' i).continuous)
    (fun i j => (bs i j).continuous) x X Y T hXc hYc
    hXsol hYsol τ hτ hτT R Kc Ks
    hXb hYb hDrift bs
  filter_upwards [hXX₀,hYY₀,hsame] with ω hXω hYω hω
  intro t ht hbefore
  have hτt : t ≤ τ ω := by
    by_contra hn
    have hlt : τ ω < t := lt_of_not_ge hn
    have hτltT : τ ω < T := hlt.trans_le ht
    have hmem := (firstClosedHit_isLeast Z T 1 ω (hZc ω)).1
    have hlevel : 1 ≤ Z (τ ω) ω := by
      rcases hmem with hlevel | hterminal
      · exact hlevel.2
      · exact False.elim ((ne_of_lt hτltT) hterminal)
    have hbefore' := hbefore (τ ω) hlt
    change z (X₀ (τ ω) ω) < 1 at hbefore'
    rw [← hXω (τ ω)] at hbefore'
    exact not_lt_of_ge hlevel hbefore'
  have heq := hω t ht
  simp only [stoppedState,min_eq_left hτt] at heq
  change X₀ t ω = Y₀ t ω
  rw [hXω t,hYω t] at heq
  exact heq

end SlowEquilibration.SphericalC1LocalAgreement
