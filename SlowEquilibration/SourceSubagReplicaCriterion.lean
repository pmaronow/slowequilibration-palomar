-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagReplicaExclusion
public import SlowEquilibration.SourceLiteratureStrictTAPGap
public import SlowEquilibration.ThermalPhysicalZeroContact
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! Source `thm:th-subag`: the TAP equality criterion and the zero-limsup
replica criterion, with `log 0 = -∞`. The existing positive-overlap
Theorem 5 and Remark 25 interfaces remain explicit hypotheses. The zero
endpoint is obtained from the existing Theorem 10 forward interface and
the proved general zero-contact lemma. The physical TAP expression at zero
uses `E(0) = 0` and `F_res(β,0) = F(β)` rather than unconstrained fields of
`ThermodynamicData`.

For source `lem:th-replica-exclusion`, this module proves the printed count
and tolerance normalization for every non-multisamplable positive overlap,
and applies it to strict physical TAP gaps and certified noncontacts. The
general positive-potential-to-strict-TAP-gap theorem outside the certificate
phase is a separate gap; no such implication is assumed silently here. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSubagReplicaCriterion

open MeasureTheory Filter Set
open SphericalModel SphericalTAPCertificate CrisantiSommers
open LiteratureSubagPhysicalDefinitions LiteratureSubagTAP LiteratureSubagReplicaExclusion
open LiteratureSubagContact SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureStrictTAPGap
open scoped Topology
set_option autoImplicit false

/-- Extended logarithmic rate of the literal annealed replica probability.
Zero probability has rate `-∞`, including in zero dimension. -/
def replicaLogRate (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) : EReal :=
  if expectedOverlapBlockProbability N k μ β q ρ = 0 then ⊥
  else (Real.log (expectedOverlapBlockProbability N k μ β q ρ) / (N : ℝ) : ℝ)

/-- Extend the physical TAP value to the source endpoint using its actual
ground and residual values, which the existing data constrain only on `(0,1)`. -/
def sourceTAPValue {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (q : ℝ) : ℝ :=
  if q = 0 then β * 0 + Real.log (1 - q) / 2 + D.pressure else tapValue D q

private theorem zero_multiSamplable {μ : FiniteMixture} {β : ℝ}
    (h10 : Theorem10Forward μ β) : MultiSamplable μ β 0 := by
  apply h10.2 0
  refine ⟨by norm_num, ?_⟩
  have hmax := (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero μ β
    (CSParisiMeasure.canonicalMinimizer μ β)
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β)).1
  intro r hr
  simpa only [firstVariation, μ.xi_zero, mul_zero,
    intervalIntegral.integral_same, sub_self] using hmax r hr

/-- Source `thm:th-subag`(1) for the whole printed interval `[0,1)`.
Theorem 10 is used only to supply the endpoint omitted by the existing
positive-overlap Theorem 5 signature. -/
theorem source_subag_tap {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (h5 : Theorem5 D)
    (h10 : Theorem10Forward μ β) {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = sourceTAPValue D q ↔ MultiSamplable μ β q) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [sourceTAPValue, ite_true, sub_zero, Real.log_one, zero_div,
      mul_zero, zero_add]
    exact ⟨le_rfl, iff_of_true True.intro (zero_multiSamplable h10)⟩
  · have hpos : q ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩
    simpa only [sourceTAPValue, ite_eq_right hq0] using
      And.intro (h5.2 q hpos).2 (h5.2 q hpos).1

private theorem replicaLogRate_le_of_exponential {N k : ℕ} {μ : FiniteMixture}
    {β q ρ c : ℝ} (hN : 0 < N)
    (hb : expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ))) :
    replicaLogRate N k μ β q ρ ≤ ((-c : ℝ) : EReal) := by
  unfold replicaLogRate
  split_ifs with hp
  · exact bot_le
  · have hp0 : 0 < expectedOverlapBlockProbability N k μ β q ρ :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
    have hlog := Real.log_le_log hp0 hb
    rw [Real.log_exp] at hlog
    apply EReal.coe_le_coe_iff.mpr
    exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr hlog

/-- Source `thm:th-subag`(2), with its correct extended-real logarithm.
The converse is proved too, from the repository's positivity-aware definition
of multisamplability. The zero endpoint again uses Theorem 10 alone. -/
theorem source_replica_criterion {μ : FiniteMixture} {β q : ℝ}
    (h25 : Remark25Contrapositive μ β) (h10 : Theorem10Forward μ β)
    (hq : q ∈ Ico (0 : ℝ) 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => replicaLogRate N k μ β q ρ) atTop = 0) ↔
      MultiSamplable μ β q := by
  constructor
  · intro hcrit
    by_cases hq0 : q = 0
    · subst q
      exact zero_multiSamplable h10
    · by_contra hn
      obtain ⟨k, hk, ρ, hρ, c, hc, hb⟩ := h25.2 q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩ hn
      have hr : ∀ᶠ N : ℕ in atTop,
          replicaLogRate N k μ β q ρ ≤ ((-c : ℝ) : EReal) := by
        filter_upwards [hb, eventually_gt_atTop 0] with N hN hNpos
        exact replicaLogRate_le_of_exponential hNpos hN
      have hlim := limsup_le_of_le (h := hr)
      rw [hcrit k hk ρ hρ] at hlim
      have hneg : ((-c : ℝ) : EReal) < 0 := by
        exact_mod_cast neg_neg_of_pos hc
      exact (not_le_of_gt hneg) hlim
  · intro hm k hk ρ hρ
    obtain ⟨hp, ht⟩ := hm k hk ρ hρ
    have ht' := EReal.tendsto_coe.mpr ht
    apply Filter.Tendsto.limsup_eq
    apply ht'.congr'
    filter_upwards [hp] with N hN
    simp only [replicaLogRate, ite_eq_right hN.ne']

private theorem block_probability_singleton (N : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : expectedOverlapBlockProbability N 1 μ β q ρ = 1 := by
  have hevent : {σ : Fin 1 → Vector N |
      ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ} = univ := by
    ext σ
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  rw [expectedOverlapBlockProbability, hevent, probReal_univ]

private theorem block_probability_mono {N k : ℕ} (μ : FiniteMixture)
    (β q : ℝ) {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    expectedOverlapBlockProbability N k μ β q ρ ≤
      expectedOverlapBlockProbability N k μ β q σ := by
  unfold expectedOverlapBlockProbability
  exact measureReal_mono (fun v hv i j hij => (hv i j hij).trans_le hρσ)

/-- The printed `k ≥ 2` and `ρ ∈ (0,1)` follow from the actual one-replica
probability being one and tolerance monotonicity, with the same decay rate. -/
theorem source_normalized_replica_exclusion {μ : FiniteMixture} {β q : ℝ}
    (h25 : Remark25Contrapositive μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hn : ¬ MultiSamplable μ β q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨k, hk, ρ, hρ, c, hc, hb⟩ := h25.2 q hq hn
  have hk2 : 2 ≤ k := by
    by_contra hknot
    have hk1 : k = 1 := by omega
    subst k
    obtain ⟨N, hN, hNpos⟩ := (hb.and (eventually_gt_atTop 0)).exists
    rw [block_probability_singleton] at hN
    have hneg : -c * (N : ℝ) < 0 := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      nlinarith
    exact (not_le_of_gt (Real.exp_lt_one_iff.mpr hneg)) hN
  refine ⟨k, hk2, min ρ (1 / 2), ⟨lt_min hρ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, c, hc, ?_⟩
  filter_upwards [hb] with N hN
  exact (block_probability_mono μ β q (min_le_left _ _)).trans hN

/-- Printed replica normalization at any strict physical TAP gap, without
a restriction to the one-step certificate phase. -/
theorem source_replica_exclusion_of_strict_tap_gap {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (h5 : Theorem5 D)
    (h25 : Remark25Contrapositive μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
  source_normalized_replica_exclusion h25 hq
    (not_multiSamplable_of_strictTAPGap D h5 hq hgap)

/-- Source `lem:th-replica-exclusion` in the certified phase, at every
positive canonical potential. The strict physical gap uses only Chen and
Chen--Sen; exclusion uses the existing Subag interfaces. -/
theorem source_replica_exclusion_of_positive_potential
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    {μ : FiniteMixture} {β x Q q : ℝ} (h : Certificate μ β x Q)
    (D : ThermodynamicData μ β) (h5 : Theorem5 D)
    (h25 : Remark25Contrapositive μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  have hqQ : q ≠ Q := by
    intro heq
    rw [heq, h.canonical_law, h.contact_value] at hV
    exact (lt_irrefl 0) hV
  exact source_replica_exclusion_of_strict_tap_gap D h5 h25 hq
    (strictTAPGap_of_literature hChen hChenSen h D q hq hqQ)

end SlowEquilibration.SourceSubagReplicaCriterion
