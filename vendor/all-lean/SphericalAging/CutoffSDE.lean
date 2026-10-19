module

public import SphericalAging.LocalSDE

public section

/-! Actual compact cutoffs of the manuscript's finite-N Hamiltonian drift
and projection-noise matrix, instantiated in the proved local SDE theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CutoffSDE
open HardSphereDynamics LocalSDE
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def cutoffDrift (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (i : Fin N) (x : State N) : ℝ := (cutoffCoefficient R hR (hamiltonianDrift β J) x) i

@[expose] def cutoffNoise (N : ℕ) (R : ℝ) (hR : 0 < R) (i j : Fin N) (x : State N) : ℝ :=
  (cutoffCoefficient R hR (fun x => noiseColumn x j) x) i

theorem coordinate_lipschitz (i : Fin N) : LipschitzWith 1 (fun x : State N => x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul] using PiLp.dist_apply_le x y i

theorem cutoffDrift_lipschitz (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ i, LipschitzWith K (cutoffDrift β J R hR i) := by
  obtain ⟨K, hK⟩ := cutoffCoefficient_lipschitz R hR (hamiltonianDrift β J)
    ((contDiff_hamiltonianDrift β J).of_le (by simp))
  refine ⟨K, fun i => ?_⟩
  change LipschitzWith K (fun x => (cutoffCoefficient R hR (hamiltonianDrift β J) x) i)
  simpa only [one_mul, Function.comp_def] using (coordinate_lipschitz i).comp hK

theorem cutoffNoise_lipschitz (N : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ i j, LipschitzWith K (cutoffNoise N R hR i j) := by
  have hex : ∀ j : Fin N, ∃ K : ℝ≥0,
      LipschitzWith K (cutoffCoefficient R hR (fun x : State N => noiseColumn x j)) :=
    fun j => cutoffCoefficient_lipschitz R hR _ ((contDiff_noiseColumn j).of_le (by simp))
  choose K hK using hex
  refine ⟨∑ j : Fin N, K j, fun i j => ?_⟩
  have hle : K j ≤ ∑ k : Fin N, K k :=
    Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ K k)) (Finset.mem_univ j)
  change LipschitzWith (∑ k : Fin N, K k)
    (fun x => (cutoffCoefficient R hR (fun x => noiseColumn x j) x) i)
  simpa only [one_mul, Function.comp_def] using
    ((coordinate_lipschitz i).comp (hK j)).weaken (by simpa only [one_mul] using hle)

theorem cutoffDrift_bounded (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, ∀ i x, ‖cutoffDrift β J R hR i x‖ ≤ K := by
  obtain ⟨K, hK⟩ := cutoffCoefficient_bounded R hR (hamiltonianDrift β J)
    (contDiff_hamiltonianDrift β J).continuous
  exact ⟨K, fun i x => (PiLp.norm_apply_le _ i).trans (hK x)⟩

theorem cutoffNoise_bounded (N : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ i j x, ‖cutoffNoise N R hR i j x‖ ≤ K := by
  have hex : ∀ j : Fin N, ∃ K : ℝ, ∀ x,
      ‖cutoffCoefficient R hR (fun x : State N => noiseColumn x j) x‖ ≤ K :=
    fun j => cutoffCoefficient_bounded R hR _ (contDiff_noiseColumn j).continuous
  choose K hK using hex
  let M : Fin N → ℝ≥0 := fun j => ⟨max (K j) 0, le_max_right _ _⟩
  refine ⟨∑ j : Fin N, M j, fun i j x => ?_⟩
  calc
    _ ≤ K j := (PiLp.norm_apply_le _ i).trans (hK j x)
    _ ≤ (M j : ℝ) := le_max_left _ _
    _ ≤ _ := by exact_mod_cast Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ M k)) (Finset.mem_univ j)

theorem cutoffDrift_eq (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (x : State N) (hx : ‖x‖ ≤ R) (i : Fin N) :
    cutoffDrift β J R hR i x = (hamiltonianDrift β J x) i := by
  simp only [cutoffDrift, cutoffCoefficient_eq R hR _ x hx]

theorem cutoffNoise_eq (N : ℕ) (R : ℝ) (hR : 0 < R)
    (x : State N) (hx : ‖x‖ ≤ R) (i j : Fin N) :
    cutoffNoise N R hR i j x = (noiseColumn x j) i := by
  simp only [cutoffNoise, cutoffCoefficient_eq R hR _ x hx]

/-- Genuine local strong solution for the actual finite-N cutoff Hamiltonian
SDE. All Lipschitz premises are proved from the manuscript's coefficients. -/
theorem exists_cutoff_hamiltonian_strongSolution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (x0 : State N) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ X : ℝ≥0 → Ω → State N,
      ∃ hsigma : ∀ i j, Continuous (cutoffNoise N R hR i j),
        IsLocalStrongSolutionOn (cutoffDrift β J R hR) (cutoffNoise N R hR) hsigma D x0 X T := by
  obtain ⟨Kb, hb⟩ := cutoffDrift_lipschitz β J R hR
  obtain ⟨Ks, hsigma⟩ := cutoffNoise_lipschitz N R hR
  obtain ⟨T, hT, X, hX⟩ := exists_local_strongSolution D hb hsigma x0
  exact ⟨T, hT, X, (fun i j => (hsigma i j).continuous), hX⟩

end SphericalAging.CutoffSDE
