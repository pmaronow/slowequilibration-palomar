module

public import SphericalAging.MultivariateTaylorPartition
public import SphericalAging.SDEWeightedCovariation

public section

/-! Actual finite-dimensional Taylor partition sums and their genuine
weighted Hessian bracket limits for the constructed strong SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MultivariateItoSums
open HardSphereDynamics LocalSDE MultivariateTaylor MultivariateTaylorPartition
open VectorItoFormula WeightedVectorQuadratic LocalWeightedQuadratic SDEWeightedCovariation
open AnnealedSDECore
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*}

@[expose] def linearApprox (f : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range n,fderiv ℝ f (X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)

@[expose] def quadraticApprox (f : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range n,(1/2 : ℝ)*Hessian f (X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)

/-- Exact finite partition identity before any stochastic limit. -/
lemma partition_identity (f : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (hn : 0<n) (ω : Ω) :
    f (X t ω)-f (X 0 ω)=linearApprox f X t n ω+quadraticApprox f X t n ω+remainderApprox f X t n ω := by
  have hsum : ∑ l ∈ Finset.range n,(f (X (uniformPartitionTime t n (l+1)) ω)-
      f (X (uniformPartitionTime t n l) ω))=f (X t ω)-f (X 0 ω) := by
    rw [Finset.sum_range_sub (fun l => f (X (uniformPartitionTime t n l) ω)) n]
    have hn0 : (n : ℝ≥0)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    simp [uniformPartitionTime,hn0]
  rw [← hsum]
  unfold linearApprox quadraticApprox remainderApprox remainder
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by ring)

lemma normQuadraticApprox_coordinates (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    normQuadraticApprox X t n ω=∑ i : Fin N,weightedQuadraticSum (fun _ _ => 1) (fun s ω => X s ω i) t n ω := by
  unfold normQuadraticApprox weightedQuadraticSum
  simp only [one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simpa only [PiLp.sub_apply] using (coordinate_square_sum
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)).trans
      (real_inner_self_eq_norm_sq _) |>.symm

lemma quadraticApprox_coordinates (f : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : quadraticApprox f X t n ω=(1/2 : ℝ)*
      ∑ i : Fin N,∑ k : Fin N,weightedCovariationSum
        (fun s ω => Hessian f (X s ω) (basisVector i) (basisVector k))
        (fun s ω => X s ω i) (fun s ω => X s ω k) t n ω := by
  let q (i k : Fin N) (l : ℕ) : ℝ := (1/2 : ℝ)*
    Hessian f (X (uniformPartitionTime t n l) ω) (basisVector i) (basisVector k)*
    (X (uniformPartitionTime t n (l+1)) ω i-X (uniformPartitionTime t n l) ω i)*
    (X (uniformPartitionTime t n (l+1)) ω k-X (uniformPartitionTime t n l) ω k)
  calc
    _ = ∑ l ∈ Finset.range n,∑ i : Fin N,∑ k : Fin N,q i k l := by
      unfold quadraticApprox
      apply Finset.sum_congr rfl
      intro l _
      rw [SphereGenerator.bilinear_coordinates]
      simp only [Finset.mul_sum,PiLp.sub_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [q]
      ring
    _ = ∑ i : Fin N,∑ k : Fin N,∑ l ∈ Finset.range n,q i k l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      unfold weightedCovariationSum
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [q]
      ring

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The norm quadratic variation input is derived from the actual SDE
coordinate equations and their physical noise rows. -/
theorem strong_normQuadratic_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) (t : ℝ≥0) (ht : t≤T) :
    TendstoInMeasure P (fun n => normQuadraticApprox X t (n+1)) atTop
      (fun ω => ∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        (∑ j : Fin N,sigma ω i j (X s ω)^2) ∂nonnegativeLebesgueMeasure) := by
  have hi := tendstoInMeasure_finsetSum Finset.univ
    (fun i n => weightedQuadraticSum (fun _ _ => 1) (fun s ω => X s ω i) t (n+1))
    (fun i ω => ∫ s in Ioc (0 : ℝ≥0) t,(∑ j : Fin N,sigma ω i j (X s ω)^2) ∂nonnegativeLebesgueMeasure)
    (fun i _ => by simpa only [one_mul] using (strong_coordinate_weightedQuadratic_tendsto D T hX t ht i
      (fun _ _ => 1) (fun _ => aestronglyMeasurable_const) (.of_forall (fun _ => continuous_const))))
  exact hi.congr_left (fun n => .of_forall (fun ω => (normQuadraticApprox_coordinates X t (n+1) ω).symm))

/-- Full multivariate Taylor error closure for the genuine actual SDE,
with no quadratic variation or Itô formula assumed as a premise. -/
theorem strong_remainder_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) (t : ℝ≥0) (ht : t≤T)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    TendstoInMeasure P (fun n => remainderApprox f X t (n+1)) atTop (fun _ => 0) := by
  apply remainder_tendstoInMeasure hf X t _
    (fun s => ((hX.2.1 s).mono (F.le s)).aestronglyMeasurable)
    (hX.2.2.1.mono (fun _ h => h.continuousOn))
  exact strong_normQuadratic_tendsto D T hX t ht

lemma hessian_basis_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (i k : Fin N) :
    Continuous (fun x => Hessian f x (basisVector i) (basisVector k)) :=
  ((hessian_continuous hf).clm_apply continuous_const).clm_apply continuous_const

/-- The second-order partition sums converge to the genuine physical
matrix covariance contracted with the Hessian of the C² observable. -/
theorem strong_quadratic_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T)
    (hsigma : ∀ ω i j,Continuous (sigma ω i j)) (t : ℝ≥0) (ht : t≤T)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    TendstoInMeasure P (fun n => quadraticApprox f X t (n+1)) atTop
      (fun ω => (1/2 : ℝ)*∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        Hessian f (X s ω) (basisVector i) (basisVector k)*
          (∑ j : Fin N,sigma ω i j (X s ω)*sigma ω k j (X s ω)) ∂nonnegativeLebesgueMeasure) := by
  have h (i k : Fin N) := strong_coordinate_weightedCovariation_tendsto D T hX hsigma t ht i k
    (fun s ω => Hessian f (X s ω) (basisVector i) (basisVector k))
    (fun s => (hessian_basis_continuous hf i k).comp_aestronglyMeasurable
      (((hX.2.1 s).mono (F.le s)).aestronglyMeasurable))
    (hX.2.2.1.mono (fun _ h => (hessian_basis_continuous hf i k).comp h))
  have hsum := tendstoInMeasure_finsetSum Finset.univ _ _ (fun i _ =>
    tendstoInMeasure_finsetSum Finset.univ _ _ (fun k _ => h i k))
  apply (hsum.const_mul_real_noMeas (1/2 : ℝ)).congr_left
  intro n
  exact .of_forall (fun ω => (quadraticApprox_coordinates f X t (n+1) ω).symm)

end SphericalAging.MultivariateItoSums
