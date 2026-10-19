-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceSourceUncutTrueRate
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorLaw
public import SlowEquilibration.SourceMixedCenteredTrueEntranceTransfer
public import Mathlib.Analysis.Normed.Group.Bounded

/-! The compact mark rectangle for an arbitrary deterministic center
sequence. The cap and horizon are fixed before every energy-window width. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedGeneralCPTransferMarks

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalMarkedWindows SphericalGaussianJet
open ConditionedEntrance ConditionedDeterminantMoments
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceMixedCenteredTrueEntranceTransfer
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- No logarithmic correction or special analytic center is required:
normalized convergence puts every fixed energy window into one rectangle. -/
theorem normalized_center_window_bounds (m : ℕ → ℝ) (E : ℝ)
    (hm : Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E))
    (M : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ((n+2:ℕ):ℝ)*(E-1) ≤ m n-M ∧
      m n+M ≤ ((n+2:ℕ):ℝ)*(E+1) := by
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hM : Tendsto (fun n : ℕ => M/((n+2:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hlo : Tendsto (fun n : ℕ => (m n-M)/((n+2:ℕ):ℝ)) atTop (𝓝 E) := by
    simpa only [sub_div, sub_zero] using hm.sub hM
  have hhi : Tendsto (fun n : ℕ => (m n+M)/((n+2:ℕ):ℝ)) atTop (𝓝 E) := by
    simpa only [add_div, add_zero] using hm.add hM
  filter_upwards [hlo.eventually_const_lt (by linarith : E-1 < E),
    hhi.eventually (gt_mem_nhds (by linarith : E < E+1))] with n hnlo hnhi
  have hn : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
  constructor
  · have hh := (lt_div_iff₀ hn).mp hnlo
    nlinarith
  · have hh := (div_lt_iff₀ hn).mp hnhi
    nlinarith

/-- The ordinary whole-field posterior entrance rate on the original
compact radial window and any center converging after normalization.
Its constants and horizon precede the fixed window half-width. -/
theorem source_mixed_general_ordinary_rate_all_small_scales
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hnp : μ.minDegree < μ.maxDegree)
    (hβ : 0 ≤ β) (U : Set ℝ) (hU : IsCompact U) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ}, 0 < a → a ≤ aStar →
        ∃ (γ c C : ℝ), 0 < γ ∧ 0 < c ∧ 0 < C ∧
          ∀ (m : ℕ → ℝ),
            Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
            ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
            ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
              (z : EuclideanSpace ℝ (Fin 2)),
              z ∈ physicalEnergyWindow (n+2) (Icc (m n-M) (m n+M)) U →
              (∫ J, originalTrueCapHitProbability μ β
                (exponentialGridHorizon γ (n+2)) a u J
                ∂mixedLaw μ Q u hu z) ≤
                C*(((n+2:ℕ):ℝ)^(1-(μ.minDegree:ℝ)/2)+
                  ((n+2:ℕ):ℝ)^(3-(μ.minDegree:ℝ)))+
                  Real.exp (-c*((n+2:ℕ):ℝ)) := by
  obtain ⟨B,hB,hUB⟩ := hU.isBounded.exists_pos_norm_le
  let Bmark := max (|E|+2) B
  have hBmark : 0 ≤ Bmark := by dsimp [Bmark]; positivity
  obtain ⟨aStar,hStar,hScales⟩ :=
    sourceUncut_fixed_axis_cap_hit_source_rate_all_small_scales
      μ hd hQ hQ1 hnp hBmark hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨γ,c,C,hγ,hc,hC,hRate⟩ := hScales ha hab
  refine ⟨γ,c,C,hγ,hc,hC,?_⟩
  intro m hm M _hM
  have hRate' : ∀ᶠ n : ℕ in atTop,
      ∀ (e k : ℝ), |e| ≤ Bmark → |k| ≤ Bmark →
      ∀ (u : Vector (n+2)), OnSphere u →
      (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
        (fun _ => 1) contDiff_const β
        (exponentialGridHorizon γ (n+2)) (J,(u,(e,k)))
        ∂disorderLaw (n+2) μ.maxDegree) ≤
        C*(((n+2:ℕ):ℝ)^(1-(μ.minDegree:ℝ)/2)+
          ((n+2:ℕ):ℝ)^(3-(μ.minDegree:ℝ)))+
          Real.exp (-c*((n+2:ℕ):ℝ)) := by
    obtain ⟨n0,hn0⟩ := eventually_atTop.1 hRate
    refine eventually_atTop.2 ⟨n0,?_⟩
    intro n hn
    simpa only [show n+1+1=n+2 by omega] using hn0 (n+1) (by omega)
  filter_upwards [normalized_center_window_bounds m E hm M,hRate'] with n hwindow hrate
  intro u hu z hz
  have hz' : ((n+2:ℕ):ℝ)*z 0 ∈ Icc (m n-M) (m n+M) ∧ z 1 ∈ U := hz
  have hn : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
  have he0 : E-1 ≤ z 0 := by nlinarith [hwindow.1,hz'.1.1]
  have he1 : z 0 ≤ E+1 := by nlinarith [hwindow.2,hz'.1.2]
  have he : |z 0| ≤ Bmark := by
    have hb : |E|+1 ≤ Bmark := by
      dsimp [Bmark]
      linarith [le_max_left (|E|+2) B]
    apply abs_le.mpr
    constructor <;> nlinarith [neg_le_abs E,le_abs_self E]
  have hk : |z 1| ≤ Bmark := by
    have hh : |z 1| ≤ B := by simpa only [Real.norm_eq_abs] using hUB (z 1) hz'.2
    exact hh.trans (le_max_right _ _)
  let e := (scorePairEquiv.symm z).1
  let k := (scorePairEquiv.symm z).2
  have hpair : scorePairEquiv (e,k) = z := by
    simpa only [e,k,Prod.mk.eta] using scorePairEquiv.apply_symm_apply z
  have heq : e = z 0 := by rw [← hpair]; simp [scorePairEquiv_apply]
  have hkq : k = z 1 := by rw [← hpair]; simp [scorePairEquiv_apply]
  have hsource := hrate e k (by simpa only [heq] using he)
    (by simpa only [hkq] using hk) u ((onSphere_iff_norm_sq u).mpr hu)
  have hLaw := originalTrueCapHitProbability_mixedPalm_integral_eq_source_one
    (n+1) μ hQ hnp u (by simpa only [show n+1+1=n+2 by omega] using hu)
    e k (2*a) β (exponentialGridHorizon γ (n+2))
  have hhalf : (2*a)/2 = a := by ring
  have hLaw' : (∫ J, originalTrueCapHitProbability μ β
      (exponentialGridHorizon γ (n+2)) a u J ∂mixedLaw μ Q u hu z) =
      ∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
        (fun _ => 1) contDiff_const β
        (exponentialGridHorizon γ (n+2)) (J,(u,(e,k)))
        ∂disorderLaw (n+2) μ.maxDegree := by
    rw [← hpair]
    simpa only [hhalf,show n+1+1=n+2 by omega,mixedLaw,mixedConditionedLaw] using hLaw
  exact hLaw'.le.trans hsource

end SlowEquilibration.SourceMixedGeneralCPTransferMarks
