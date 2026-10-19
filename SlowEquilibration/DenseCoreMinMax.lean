-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FormMinMaxQuotient

@[expose] public section

namespace SlowEquilibration.FormMinMax

open Module Set Filter Function
open scoped Topology InnerProductSpace BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual finite linear combination used to approximate a trial space. -/
def synthesis {m : ℕ} (v : Fin m → F) (a : Fin m → ℝ) : F := ∑ i, a i • v i

omit [CompleteSpace H] [CompleteSpace F] in
theorem formEnergy_smul (J : F →L[ℝ] H) (c : ℝ) (u : F) :
    formEnergy J (c • u) = c^2 * formEnergy J u := by
  unfold formEnergy
  rw [map_smul, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [CompleteSpace H] [CompleteSpace F] in
theorem synthesis_smul {m : ℕ} (v : Fin m → F) (c : ℝ) (a : Fin m → ℝ) :
    synthesis v (c • a) = c • synthesis v a := by
  simp only [synthesis, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

omit [CompleteSpace H] [CompleteSpace F] in
/-- A uniform actual Rayleigh bound on the compact coefficient unit sphere
extends to every vector by the true quadratic homogeneity. -/
theorem synthesis_bound_of_unit_sphere {m : ℕ} (J : F →L[ℝ] H) (v : Fin m → F)
    (c : ℝ) (hunit : ∀ a : Fin m → ℝ, ‖a‖ = 1 →
      formEnergy J (synthesis v a) ≤ c*‖J (synthesis v a)‖^2) (a : Fin m → ℝ) :
    formEnergy J (synthesis v a) ≤ c*‖J (synthesis v a)‖^2 := by
  by_cases ha : a = 0
  · simp [ha, synthesis, formEnergy]
  · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hnorm : ‖‖a‖⁻¹ • a‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le),
        inv_mul_cancel₀ hn.ne']
    have h := hunit (‖a‖⁻¹ • a) hnorm
    rw [synthesis_smul, formEnergy_smul, map_smul, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs] at h
    have hpos : 0 < (‖a‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr hn)
    have h' : (‖a‖⁻¹)^2 * formEnergy J (synthesis v a) ≤
        (‖a‖⁻¹)^2 * (c*‖J (synthesis v a)‖^2) := by nlinarith [h]
    exact (mul_le_mul_iff_right₀ hpos).mp h'

/-- A true finite-dimensional trial space contained in a prescribed core. -/
def CoreRayleighTrialBound (J : F →L[ℝ] H) (core : Submodule ℝ F) (k : ℕ) (c : ℝ) : Prop :=
  ∃ U : Submodule ℝ F, U ≤ core ∧ FiniteDimensional ℝ U ∧ finrank ℝ U = k+1 ∧
    ∀ u ∈ U, formEnergy J u ≤ c*‖J u‖^2

/-- Min-max restricted to genuine finite-dimensional trial spaces in the
specified core. -/
def coreRayleighMinMax (J : F →L[ℝ] H) (core : Submodule ℝ F) (k : ℕ) : ℝ :=
  sInf {c | CoreRayleighTrialBound J core k c}

/-- Approximation of the actual first-eigenvector trial space by vectors of
an actual dense form core. Compactness of the coefficient unit sphere gives
one uniform Rayleigh bound, and openness of finite linear independence
preserves the required dimension. -/
theorem core_trial_bound_of_eigenvalue_lt (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ))
    (core : Submodule ℝ F) (hdense : Dense (core : Set F)) (k : ℕ) (c : ℝ)
    (hc : weight μ k < c) : CoreRayleighTrialBound J core k c := by
  classical
  let v₀ : Fin (k+1) → F := fun i => eigenPreimage J b μ i.val
  have hli : LinearIndependent ℝ v₀ := by
    apply LinearIndependent.of_comp J.toLinearMap
    simpa only [v₀, Function.comp_def, ContinuousLinearMap.coe_coe,
      eigenPreimage_image J b μ hμ he] using
      b.orthonormal.linearIndependent.comp (fun i : Fin (k+1) => i.val) Fin.val_injective
  have hzero (a : Fin (k+1) → ℝ) (hz : synthesis v₀ a = 0) : a = 0 := by
    ext i
    exact (Fintype.linearIndependent_iff.mp hli a hz) i
  have hmem (a : Fin (k+1) → ℝ) : synthesis v₀ a ∈ trialSpace J b μ k := by
    apply Submodule.sum_mem
    intro i hi
    exact (trialSpace J b μ k).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstrict (a : Fin (k+1) → ℝ) (ha : ‖a‖ = 1) :
      formEnergy J (synthesis v₀ a) < c*‖J (synthesis v₀ a)‖^2 := by
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
    have hu0 : synthesis v₀ a ≠ 0 := fun hz => ha0 (hzero a hz)
    have hJu : J (synthesis v₀ a) ≠ 0 := by
      intro hz
      exact hu0 (hJ (hz.trans (map_zero J).symm))
    exact (formEnergy_le_on_trialSpace J hJ b μ hμ he hmono k _ (hmem a)).trans_lt
      (mul_lt_mul_of_pos_right hc (sq_pos_of_pos (norm_pos_iff.mpr hJu)))
  have hcont : Continuous (fun z : (Fin (k+1) → F) × (Fin (k+1) → ℝ) =>
      formEnergy J (synthesis z.1 z.2) - c*‖J (synthesis z.1 z.2)‖^2) := by
    unfold formEnergy synthesis
    fun_prop
  have hnear : ∀ᶠ v in 𝓝 v₀, ∀ a ∈ Metric.sphere (0 : Fin (k+1) → ℝ) 1,
      formEnergy J (synthesis v a) < c*‖J (synthesis v a)‖^2 := by
    apply (isCompact_sphere (0 : Fin (k+1) → ℝ) 1).eventually_forall_of_forall_eventually
    intro a ha
    have ha' : ‖a‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ha
    have hlt : formEnergy J (synthesis v₀ a)-c*‖J (synthesis v₀ a)‖^2 < 0 :=
      sub_neg.mpr (hstrict a ha')
    have ht := (hcont.tendsto (v₀, a)).eventually (gt_mem_nhds hlt)
    exact ht.mono (fun z hz => sub_neg.mp hz)
  have hseq (i : Fin (k+1)) : ∃ v : ℕ → F, (∀ n, v n ∈ core) ∧
      Tendsto v atTop (𝓝 (v₀ i)) :=
    mem_closure_iff_seq_limit.mp (hdense (v₀ i))
  choose v hv htv using hseq
  have ht : Tendsto (fun n i => v i n) atTop (𝓝 v₀) := tendsto_pi_nhds.mpr htv
  obtain ⟨n, hn, hlin⟩ := (ht.eventually hnear |>.and (ht.eventually hli.eventually)).exists
  let U := Submodule.span ℝ (Set.range (fun i : Fin (k+1) => v i n))
  refine ⟨U, ?_, Module.Finite.span_of_finite ℝ (Set.finite_range _), ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i n
  · change finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin (k+1) => v i n))) = k+1
    rw [finrank_span_eq_card hlin, Fintype.card_fin]
  · intro u hu
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
    apply synthesis_bound_of_unit_sphere J (fun i => v i n) c
    intro a ha
    exact (hn a (by simpa only [Metric.mem_sphere, dist_zero_right] using ha)).le

/-- Genuine equality of dense-core min-max and the actual ordered form
eigenvalue. In particular it requires no eigenfunction smoothness and does
not assert that a core trial space attains the infimum. -/
theorem coreRayleighMinMax_eq_weight (J : F →L[ℝ] H) (hJ : Injective J)
    (b : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (he : ∀ j, J (J.adjoint (b j)) = μ j • b j) (hmono : Monotone (weight μ))
    (core : Submodule ℝ F) (hdense : Dense (core : Set F)) (k : ℕ) :
    coreRayleighMinMax J core k = weight μ k := by
  have hnonempty : {c | CoreRayleighTrialBound J core k c}.Nonempty :=
    ⟨weight μ k+1, core_trial_bound_of_eigenvalue_lt J hJ b μ hμ he hmono core hdense k _
      (by linarith)⟩
  have hbelow : ∀ c, CoreRayleighTrialBound J core k c → weight μ k ≤ c := by
    intro c hc
    obtain ⟨U, hcore, hU, hdim, hb⟩ := hc
    have htrial : RayleighTrialBound J k c := ⟨U, hU, hdim, hb⟩
    rw [← rayleighMinMax_eq_weight J hJ b μ hμ he hmono k]
    exact csInf_le ⟨weight μ k, fun d hd => by
      obtain ⟨V, hV, hdimV, hboundV⟩ := hd
      let : FiniteDimensional ℝ V := hV
      by_contra hn
      have hdimle := finrank_le_of_rayleigh_bound_lt J hJ b μ hμ he hmono k d
        (lt_of_not_ge hn) V hboundV
      omega⟩ htrial
  have hbounded : BddBelow {c | CoreRayleighTrialBound J core k c} :=
    ⟨weight μ k, fun c hc => hbelow c hc⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    exact csInf_le hbounded
      (core_trial_bound_of_eigenvalue_lt J hJ b μ hμ he hmono core hdense k c hc)
  · exact le_csInf hnonempty (fun c hc => hbelow c hc)

end
end SlowEquilibration.FormMinMax
