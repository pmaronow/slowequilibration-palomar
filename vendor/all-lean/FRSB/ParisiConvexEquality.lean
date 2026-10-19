module
public import FRSB.ParisiMinimizer
public import Paper.ParisiHJBFeedback

@[expose] public section

/-! Equality in the actual measure-convexity inequality forces equality of
the two terminal control drifts, almost surely. This isolates the deterministic
strict Jensen step before the martingale nondegeneracy argument. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FRSB
open Paper

/-- Distinct terminal drifts give strict convexity for the literal payoff. -/
theorem parisiControlPayoff_mix_lt_of_drift_ne {Ω : Type*}
    (β h : ℝ) (B : Ω → ℝ) (A : ℝ → Ω → ℝ)
    (hA : ∀ ω, Measurable (fun s => A s ω)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (ω : Ω)
    (hne : parisiControlDrift β μ A ω ≠ parisiControlDrift β ν A ω) :
    parisiControlPayoff β h B A (parisiMix μ ν t) ω <
      (1 - t) * parisiControlPayoff β h B A μ ω +
        t * parisiControlPayoff β h B A ν ω := by
  have hxy : h + β * B ω + parisiControlDrift β μ A ω ≠
      h + β * B ω + parisiControlDrift β ν A ω := by
    intro he
    exact hne (add_left_cancel he)
  have hc := strictConvexOn_logCosh.2
    (mem_univ (h + β * B ω + parisiControlDrift β μ A ω))
    (mem_univ (h + β * B ω + parisiControlDrift β ν A ω)) hxy
    (sub_pos.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hc
  unfold parisiControlPayoff
  rw [parisiControlDrift_mix β μ ν A hA hb t ⟨ht.1.le, ht.2.le⟩ ω,
    parisiControlCost_mix β μ ν A hA hb t ⟨ht.1.le, ht.2.le⟩ ω]
  have he : h + β * B ω + ((1 - t) * parisiControlDrift β μ A ω +
      t * parisiControlDrift β ν A ω) =
      (1 - t) * (h + β * B ω + parisiControlDrift β μ A ω) +
        t * (h + β * B ω + parisiControlDrift β ν A ω) := by ring
  rw [he]
  linarith

/-- Equality of the actual PDE values leaves zero strict Jensen gap. -/
theorem parisiPotential_mix_eq_imp_drift_ae_eq
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : parisiPotential β (parisiMix μ ν t) (0,h) =
      (1 - t) * parisiPotential β μ (0,h) + t * parisiPotential β ν (0,h)) :
    parisiControlDrift β μ (selectedParisiControl β h hβ (parisiMix μ ν t)) =ᵐ[canonicalBrownianMeasure]
      parisiControlDrift β ν (selectedParisiControl β h hβ (parisiMix μ ν t)) := by
  let γ := parisiMix μ ν t
  let A := selectedParisiControl β h hβ γ
  have hA : IsParisiAdmissibleControl A := isParisiAdmissibleControl_selectedParisiControl β h hβ γ
  have hAm : ∀ ω, Measurable (fun s => A s ω) :=
    fun ω => hA.measurable.comp (f := fun s => (s, ω))
      (measurable_id.prodMk measurable_const)
  let G : BrownianSample → ℝ := fun ω =>
    (1 - t) * parisiControlPayoff β h (canonicalBrownian 1) A μ ω +
      t * parisiControlPayoff β h (canonicalBrownian 1) A ν ω -
        parisiControlPayoff β h (canonicalBrownian 1) A γ ω
  have hi (ρ : ParisiMeasure) := integrable_parisiControlPayoff canonicalBrownianMeasure
    β h (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one A hA.measurable hA.bounded ρ
  have hiG : Integrable G canonicalBrownianMeasure :=
    ((hi μ).const_mul (1-t) |>.add ((hi ν).const_mul t)).sub (hi γ)
  have hnonneg : ∀ ω, 0 ≤ G ω := fun ω => sub_nonneg.mpr
    (parisiControlPayoff_mix_le β h (canonicalBrownian 1) A hAm hA.bounded μ ν t
      ⟨ht.1.le, ht.2.le⟩ ω)
  have hIG : (∫ ω, G ω ∂canonicalBrownianMeasure) =
      (1 - t) * parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ +
      t * parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A ν -
        parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A γ := by
    unfold G
    rw [integral_sub
      (f := fun ω => (1-t) * parisiControlPayoff β h (canonicalBrownian 1) A μ ω +
        t * parisiControlPayoff β h (canonicalBrownian 1) A ν ω)
      (g := parisiControlPayoff β h (canonicalBrownian 1) A γ)
      ((hi μ).const_mul (1-t) |>.add ((hi ν).const_mul t)) (hi γ),
      integral_add (f := fun ω => (1-t) * parisiControlPayoff β h (canonicalBrownian 1) A μ ω)
        (g := fun ω => t * parisiControlPayoff β h (canonicalBrownian 1) A ν ω)
        ((hi μ).const_mul (1-t)) ((hi ν).const_mul t),
      integral_const_mul, integral_const_mul]
    rfl
  have hzero : (∫ ω, G ω ∂canonicalBrownianMeasure) = 0 := by
    apply le_antisymm _ (integral_nonneg hnonneg)
    rw [hIG]
    have hγ := parisiControlObjective_selected_eq_potential β h hβ γ
    have hμ := parisiControlObjective_le_potential β h hβ μ A hA
    have hν := parisiControlObjective_le_potential β h hβ ν A hA
    change parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A γ = _ at hγ
    have hm := add_le_add
      (mul_le_mul_of_nonneg_left hμ (sub_pos.mpr ht.2).le)
      (mul_le_mul_of_nonneg_left hν ht.1.le)
    dsimp only [γ] at hγ
    linarith
  have hGae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall hnonneg) hiG).mp hzero
  filter_upwards [hGae] with ω hω
  by_contra hne
  have hs := parisiControlPayoff_mix_lt_of_drift_ne β h (canonicalBrownian 1) A
    hAm hA.bounded μ ν t ht ω hne
  change G ω = 0 at hω
  dsimp only [G, γ] at hω
  linarith

/-- The correction is affine, so functional equality gives PDE-value equality. -/
theorem parisiPDEFunctional_mix_eq_imp_drift_ae_eq
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : parisiPDEFunctional β h (parisiMix μ ν t) =
      (1 - t) * parisiPDEFunctional β h μ + t * parisiPDEFunctional β h ν) :
    parisiControlDrift β μ (selectedParisiControl β h hβ (parisiMix μ ν t)) =ᵐ[canonicalBrownianMeasure]
      parisiControlDrift β ν (selectedParisiControl β h hβ (parisiMix μ ν t)) := by
  apply parisiPotential_mix_eq_imp_drift_ae_eq β h hβ μ ν t ht
  unfold parisiPDEFunctional parisiFunctional at he
  rw [parisiCorrection_integral_mix μ ν t ⟨ht.1.le, ht.2.le⟩] at he
  nlinarith

end FRSB
