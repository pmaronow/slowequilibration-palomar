module

public import SphericalAging.JointPredictableRepresentative

public section

/-! The actual Hamiltonian Picard class for arbitrary finite disorder.
Bound independence follows from uniqueness of the actual fixed-point equation.
Continuity is proved by genuine bounded-disorder neighborhoods, allowing the
constructed jointly predictable representative to handle Gaussian disorder
without imposing an artificial bounded support condition.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.GlobalHamiltonianParameter
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE
open HamiltonianPicardDependence JointPredictableRepresentative
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma predictableCoefficient_bound_independent {K L : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (hh : LipschitzWith L g)
    (U : PredictableStateL2 N F P) (T : ℝ≥0) :
    predictableCoefficient hg U T = predictableCoefficient hh U T := by
  apply Subtype.ext
  apply Lp.ext
  exact (predictableCoefficient_coeFn hg U T).trans (predictableCoefficient_coeFn hh U T).symm

lemma finiteDrift_bound_independent {K L : ℝ≥0} {g : Fin N → State N → ℝ}
    (hg : ∀ i, LipschitzWith K (g i)) (hh : ∀ i, LipschitzWith L (g i))
    (U : PredictableStateL2 N F P) (T : ℝ≥0) :
    finiteDriftPicardMap hg T U = finiteDriftPicardMap hh T U := by
  unfold finiteDriftPicardMap driftCoefficientMap
  apply Finset.sum_congr rfl
  intro i _
  rw [predictableCoefficient_bound_independent (hg i) (hh i) U T]

lemma horizonClass_drift_bound_independent (D : BrownianDriver N P F)
    {K L Ks : ℝ≥0} {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith K (b i)) (hc : ∀ i, LipschitzWith L (b i))
    (hs : ∀ i j, LipschitzWith Ks (sigma i j)) (x0 : State N) (T : ℝ≥0) :
    GlobalSDE.horizonClass D hb hs x0 T = GlobalSDE.horizonClass D hc hs x0 T := by
  apply GlobalSDE.horizonClass_unique
  rw [← finiteDrift_bound_independent hb hc]
  exact GlobalSDE.horizonClass_fixedPoint D hb hs x0 T

lemma hamiltonianClass_bound_independent (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A B T : ℝ≥0) (J : FiniteModel.Disorder N p) (hA : ‖J‖ ≤ A) (hB : ‖J‖ ≤ B) (x : State N) :
    hamiltonianClass D β R hR A T (⟨J,hA⟩,x) = hamiltonianClass D β R hR B T (⟨J,hB⟩,x) :=
  horizonClass_drift_bound_independent D _ _ _ x T

/-- Canonical actual Picard class on the full finite Gaussian disorder space. -/
@[expose] def globalClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) : PredictableStateL2 N F P :=
  hamiltonianClass D β R hR (‖q.1‖₊+1) T
    (⟨q.1,by simp⟩,q.2)

lemma globalClass_eq_bounded (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hA : ‖J‖ ≤ A) (x : State N) :
    globalClass D β R hR T (J,x) = hamiltonianClass D β R hR A T (⟨J,hA⟩,x) :=
  hamiltonianClass_bound_independent D β R hR _ A T J _ hA x

/-- Joint continuity in unrestricted disorder and initial state. -/
theorem globalClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) :
    Continuous (globalClass (p := p) D β R hR T) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let A : ℝ≥0 := ‖q.1‖₊+1
  have hqA : ‖q.1‖ ≤ A := by dsimp [A]; simp
  obtain ⟨K,hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR A T
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let δ : ℝ := min 1 (ε/((K : ℝ)+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  have hr1 : dist r q < 1 := hr.trans_le (min_le_left _ _)
  have hJdist : dist r.1 q.1 ≤ dist r q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hrA : ‖r.1‖ ≤ A := by
    have hnorm := norm_le_norm_add_norm_sub q.1 r.1
    rw [← dist_eq_norm] at hnorm
    rw [dist_comm q.1 r.1] at hnorm
    change ‖r.1‖ ≤ ‖q.1‖+1
    linarith
  rw [globalClass_eq_bounded D β R hR A T r.1 hrA r.2,
    globalClass_eq_bounded D β R hR A T q.1 hqA q.2]
  have hd : dist ((⟨r.1,hrA⟩,r.2) : BoundedDisorder N p A × State N)
      ((⟨q.1,hqA⟩,q.2) : BoundedDisorder N p A × State N) = dist r q := by
    simp only [Prod.dist_eq, Subtype.dist_eq]
  calc
    _ ≤ (K : ℝ)*dist r q := by simpa only [hd] using hK.dist_le_mul (⟨r.1,hrA⟩,r.2) (⟨q.1,hqA⟩,q.2)
    _ ≤ ((K : ℝ)+1)*dist r q := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hsmall := hr.trans_le (min_le_right _ _)
      have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < (K : ℝ)+1)).mp hsmall
      simpa only [mul_comm] using hm

/-- The actual parameter-dependent Hamiltonian Picard family admits a joint
predictable representative on the entire disorder space. -/
theorem exists_joint_predictable_globalClass (D : BrownianDriver N P F) (β R : ℝ)
    (hR : 0 < R) (T : ℝ≥0) :
    ∃ G : (FiniteModel.Disorder N p × State N) × (ℝ≥0 × Ω) → State N,
      StronglyMeasurable[(inferInstance : MeasurableSpace (FiniteModel.Disorder N p × State N)).prod F.predictable] G ∧
      ∀ q, (fun z => G (q,z)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (globalClass D β R hR T q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  exists_joint_predictable_representative _ (globalClass_continuous D β R hR T).stronglyMeasurable

end SphericalAging.GlobalHamiltonianParameter
