module

public import SphericalAging.FiniteModel
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

public section

/-! The literal Gaussian fork increment from Huang--Sellke Lemma 3.2,
for the ordered pure-p model. Its covariance is calculated under the
actual independent product disorder law. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianOrthogonalForkCovariance
open MeasureTheory ProbabilityTheory FiniteModel
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

private theorem covariance_fun_add_left {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z : Ω→ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    covariance (fun ω => X ω+Y ω) Z μ=covariance X Z μ+covariance Y Z μ :=
  covariance_add_left hX hY hZ

private theorem covariance_fun_add_right {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z : Ω→ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    covariance X (fun ω => Y ω+Z ω) μ=covariance X Y μ+covariance X Z μ :=
  covariance_add_right hX hY hZ

@[expose] abbrev ForkDisorder (N p K : ℕ) := Option (Fin K)→Disorder N p
@[expose] def forkLaw (N p K : ℕ) : Measure (ForkDisorder N p K) :=
  Measure.pi (fun _ => disorderLaw N p)
instance : IsProbabilityMeasure (forkLaw N p K) := by unfold forkLaw; infer_instance

@[expose] def block (i : Option (Fin K)) (x : Vector N) (J : ForkDisorder N p K) : ℝ :=
  Hamiltonian N p (J i) x

theorem block_memLp (i : Option (Fin K)) (x : Vector N) :
    MemLp (block i x) 2 (forkLaw N p K) :=
  (Hamiltonian_memLp x).comp_measurePreserving
    (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i)

theorem block_mean (i : Option (Fin K)) (x : Vector N) :
    ∫ J, block i x J ∂forkLaw N p K=0 := by
  exact (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i).hasLaw.integral_comp
    (Hamiltonian_memLp x).aestronglyMeasurable |>.trans (Hamiltonian_mean x)

theorem block_covariance (hN : 0<N) (hp : 1≤p)
    (i j : Option (Fin K)) (x y : Vector N) :
    covariance (block i x) (block j y) (forkLaw N p K)=
      if i=j then (N:ℝ)*(⟪x,y⟫_ℝ/N)^p else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    have hh := (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i).hasLaw.covariance_fun_comp
      (Hamiltonian_memLp x).aemeasurable (Hamiltonian_memLp y).aemeasurable
    rw [Hamiltonian_probability_covariance hN,dimension_covariance_scale N p hN hp] at hh
    exact hh
  · rw [if_neg hij]
    have hi : iIndepFun (fun i : Option (Fin K) => fun J : ForkDisorder N p K => J i)
        (forkLaw N p K) := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    exact ((hi.indepFun hij).comp
      (by unfold Hamiltonian; fun_prop : Measurable (fun J => Hamiltonian N p J x))
      (by unfold Hamiltonian; fun_prop : Measurable (fun J => Hamiltonian N p J y))).covariance_eq_zero
      (block_memLp i x) (block_memLp j y)

@[expose] def sharedIncrement (x : Vector N) (y : Fin K→Vector N) (i : Fin K)
    (J : ForkDisorder N p K) : ℝ := block none (y i) J-block none x J

@[expose] def increment (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) (i : Fin K)
    (J : ForkDisorder N p K) : ℝ :=
  Real.sqrt a*sharedIncrement x y i J+Real.sqrt (b-a)*block (some i) (y i) J

@[expose] def averagedIncrement (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) : ℝ := (∑i,increment a b x y i J)/((K:ℝ)*N)

theorem sharedIncrement_memLp (x : Vector N) (y : Fin K→Vector N) (i : Fin K) :
    MemLp (sharedIncrement x y i) 2 (forkLaw N p K) :=
  (block_memLp none (y i)).sub (block_memLp none x)

theorem increment_memLp (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) (i : Fin K) :
    MemLp (increment a b x y i) 2 (forkLaw N p K) :=
  ((sharedIncrement_memLp x y i).const_mul _).add ((block_memLp (some i) (y i)).const_mul _)

theorem increment_mean (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) (i : Fin K) :
    ∫J,increment a b x y i J ∂forkLaw N p K=0 := by
  unfold increment
  have hc := ((sharedIncrement_memLp (p := p) x y i).const_mul (Real.sqrt a)).integrable (by norm_num)
  have hf := ((block_memLp (p := p) (some i) (y i)).const_mul (Real.sqrt (b-a))).integrable (by norm_num)
  rw [integral_add hc hf]
  rw [integral_const_mul,integral_const_mul]
  unfold sharedIncrement
  rw [integral_sub ((block_memLp none (y i)).integrable (by norm_num))
    ((block_memLp none x).integrable (by norm_num)),block_mean,block_mean,block_mean]
  ring

theorem shared_covariance (hN : 0<N) (hp : 1≤p) (x : Vector N) (y : Fin K→Vector N)
    (i j : Fin K) :
    covariance (sharedIncrement x y i) (sharedIncrement x y j) (forkLaw N p K)=
      (N:ℝ)*((⟪y i,y j⟫_ℝ/N)^p-(⟪y i,x⟫_ℝ/N)^p-
        (⟪x,y j⟫_ℝ/N)^p+(⟪x,x⟫_ℝ/N)^p) := by
  unfold sharedIncrement
  rw [covariance_fun_sub_fun_sub
    (block_memLp none (y i)) (block_memLp none x)
    (block_memLp none (y j)) (block_memLp none x)]
  simp only [block_covariance hN hp,ite_true]
  ring

theorem shared_fresh_covariance (hN : 0<N) (hp : 1≤p) (x : Vector N)
    (y : Fin K→Vector N) (i j : Fin K) :
    covariance (sharedIncrement x y i) (block (some j) (y j)) (forkLaw N p K)=0 := by
  unfold sharedIncrement
  rw [covariance_fun_sub_left (block_memLp none (y i))
    (block_memLp none x) (block_memLp (some j) (y j))]
  simp [block_covariance hN hp]

theorem increment_covariance (hN : 0<N) (hp : 1≤p) (a b : ℝ) (ha : 0≤a) (hab : a≤b)
    (x : Vector N) (y : Fin K→Vector N) (i j : Fin K) :
    covariance (increment a b x y i) (increment a b x y j) (forkLaw N p K)=
      a*(N:ℝ)*((⟪y i,y j⟫_ℝ/N)^p-(⟪y i,x⟫_ℝ/N)^p-
        (⟪x,y j⟫_ℝ/N)^p+(⟪x,x⟫_ℝ/N)^p)+
      (b-a)*(if i=j then (N:ℝ)*(⟪y i,y j⟫_ℝ/N)^p else 0) := by
  have hsc := ((sharedIncrement_memLp (p := p) x y i).const_mul (Real.sqrt a))
  have hfc := ((block_memLp (p := p) (some i) (y i)).const_mul (Real.sqrt (b-a)))
  have hsd := ((sharedIncrement_memLp (p := p) x y j).const_mul (Real.sqrt a))
  have hfd := ((block_memLp (p := p) (some j) (y j)).const_mul (Real.sqrt (b-a)))
  have hz : covariance (block (some i) (y i)) (sharedIncrement x y j) (forkLaw N p K)=0 := by
    rw [covariance_comm,shared_fresh_covariance hN hp]
  change covariance
    ((fun J => Real.sqrt a*sharedIncrement x y i J)+(fun J => Real.sqrt (b-a)*block (some i) (y i) J))
    ((fun J => Real.sqrt a*sharedIncrement x y j J)+(fun J => Real.sqrt (b-a)*block (some j) (y j) J))
    (forkLaw N p K)=_
  rw [covariance_add_left hsc hfc (hsd.add hfd),covariance_add_right hsc hsd hfd,
    covariance_add_right hfc hsd hfd]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    shared_fresh_covariance hN hp,hz,shared_covariance hN hp,block_covariance hN hp,
    Option.some.injEq,mul_zero,zero_add,add_zero]
  ring_nf
  rw [Real.sq_sqrt ha,Real.sq_sqrt (sub_nonneg.mpr hab)]
  ring

/-- The actual many-orthogonal-increments geometry. -/
structure OrthogonalFork (x : Vector N) (y : Fin K→Vector N) (r q : ℝ) : Prop where
  base_norm : ‖x‖^2=(N:ℝ)*r
  leaf_norm : ∀i,‖y i‖^2=(N:ℝ)*q
  increment_base : ∀i,⟪y i-x,x⟫_ℝ=0
  increment_orthogonal : ∀i j,i≠j→⟪y i-x,y j-x⟫_ℝ=0

theorem OrthogonalFork.leaf_base {x : Vector N} {y : Fin K→Vector N} {r q : ℝ}
    (hf : OrthogonalFork x y r q) (i : Fin K) : ⟪y i,x⟫_ℝ=(N:ℝ)*r := by
  have hh := hf.increment_base i
  rw [inner_sub_left,real_inner_self_eq_norm_sq,hf.base_norm] at hh
  linarith

theorem OrthogonalFork.leaf_inner {x : Vector N} {y : Fin K→Vector N} {r q : ℝ}
    (hf : OrthogonalFork x y r q) (i j : Fin K) :
    ⟪y i,y j⟫_ℝ=(N:ℝ)*(if i=j then q else r) := by
  classical
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl,real_inner_self_eq_norm_sq,hf.leaf_norm]
  · rw [if_neg hij]
    have hb : ⟪x,y j⟫_ℝ=(N:ℝ)*r := by
      rw [real_inner_comm]; exact hf.leaf_base j
    have hh := hf.increment_orthogonal i j hij
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hf.leaf_base i,
      hb,real_inner_self_eq_norm_sq,hf.base_norm] at hh
    linarith

theorem orthogonal_increment_covariance (hN : 0<N) (hp : 1≤p) (a b : ℝ)
    (ha : 0≤a) (hab : a≤b) (x : Vector N) (y : Fin K→Vector N) (r q : ℝ)
    (hf : OrthogonalFork x y r q) (i j : Fin K) :
    covariance (increment a b x y i) (increment a b x y j) (forkLaw N p K)=
      if i=j then (N:ℝ)*(b*q^p-a*r^p) else 0 := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hb : ⟪x,y j⟫_ℝ=(N:ℝ)*r := by
    rw [real_inner_comm]; exact hf.leaf_base j
  rw [increment_covariance hN hp a b ha hab, hf.leaf_inner i j,hf.leaf_base i,
    hb,real_inner_self_eq_norm_sq,hf.base_norm]
  simp only [mul_div_cancel_left₀ _ hn]
  by_cases hij : i=j
  · simp only [if_pos hij]
    ring
  · simp only [if_neg hij]
    ring

theorem averagedIncrement_memLp (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) :
    MemLp (averagedIncrement a b x y) 2 (forkLaw N p K) := by
  change MemLp (fun J => (∑i,increment a b x y i J)/((K:ℝ)*N)) 2 (forkLaw N p K)
  simpa only [div_eq_mul_inv,mul_comm] using
    (memLp_finsetSum Finset.univ (fun i _ => increment_memLp (p := p) a b x y i)).const_mul
      (((K:ℝ)*N)⁻¹)

theorem averagedIncrement_mean (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) :
    ∫J,averagedIncrement a b x y J ∂forkLaw N p K=0 := by
  unfold averagedIncrement
  rw [integral_div,integral_finsetSum _ (fun i _ => (increment_memLp a b x y i).integrable (by norm_num))]
  simp only [increment_mean,Finset.sum_const_zero,zero_div]

theorem orthogonal_fork_variance (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (x : Vector N) (y : Fin K→Vector N) (r q : ℝ)
    (hf : OrthogonalFork x y r q) :
    variance (averagedIncrement a b x y) (forkLaw N p K)=
      (b*q^p-a*r^p)/((K:ℝ)*N) := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  unfold averagedIncrement
  simp only [←inv_mul_eq_div]
  rw [variance_const_mul,variance_fun_sum (fun i => increment_memLp a b x y i)]
  simp_rw [orthogonal_increment_covariance hN hp a b ha hab x y r q hf]
  classical
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  <;> ring

@[expose] def hamiltonianCLM (x : Vector N) : Disorder N p→L[ℝ] ℝ :=
  normalization N p • ∑ I : TensorIndex N p,tensorMonomial x I • ContinuousLinearMap.proj I

theorem hamiltonianCLM_apply (x : Vector N) (J : Disorder N p) :
    hamiltonianCLM x J=Hamiltonian N p J x := by
  simp only [hamiltonianCLM,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Hamiltonian]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

@[expose] def averagedIncrementCLM (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) :
    ForkDisorder N p K→L[ℝ] ℝ :=
  ((K:ℝ)*N)⁻¹ • ∑i : Fin K,
    (Real.sqrt a • ((hamiltonianCLM (y i)-hamiltonianCLM x).comp (ContinuousLinearMap.proj none))+
      Real.sqrt (b-a) • ((hamiltonianCLM (y i)).comp (ContinuousLinearMap.proj (some i))))

theorem averagedIncrementCLM_apply (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) : averagedIncrementCLM a b x y J=averagedIncrement a b x y J := by
  simp only [averagedIncrementCLM,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,hamiltonianCLM_apply,
    averagedIncrement,increment,sharedIncrement,block,inv_mul_eq_div]

theorem forkDisorder_hasGaussianLaw :
    HasGaussianLaw (id : ForkDisorder N p K→ForkDisorder N p K) (forkLaw N p K) := by
  have hi : iIndepFun (fun i : Option (Fin K) => fun J : ForkDisorder N p K => J i)
      (forkLaw N p K) := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hG : ∀i : Option (Fin K),HasGaussianLaw (fun J : ForkDisorder N p K => J i) (forkLaw N p K) := by
    intro i
    refine ⟨(measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i).measurable.aemeasurable,?_⟩
    change IsGaussian ((Measure.pi (fun _ : Option (Fin K) => disorderLaw N p)).map (Function.eval i))
    rw [(measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) i).map_eq]
    simpa only [Measure.map_id] using (disorder_hasGaussianLaw N p).isGaussian_map
  exact hi.hasGaussianLaw hG

theorem averagedIncrement_hasGaussianLaw (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) :
    HasGaussianLaw (averagedIncrement a b x y) (forkLaw N p K) := by
  have hh := forkDisorder_hasGaussianLaw (N := N) (p := p) (K := K) |>.map_fun
    (averagedIncrementCLM a b x y)
  simpa only [id_eq,averagedIncrementCLM_apply] using hh

theorem orthogonal_fork_variance_le (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (x : Vector N) (y : Fin K→Vector N) (r q : ℝ)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (hf : OrthogonalFork x y r q) :
    variance (averagedIncrement a b x y) (forkLaw N p K)≤1/((K:ℝ)*N) := by
  rw [orthogonal_fork_variance hN hp hK a b ha hab x y r q hf]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hpq := pow_le_one₀ hq hq1 (n := p)
  have hbr : 0≤b := ha.trans hab
  have hpr : 0≤a*r^p := mul_nonneg ha (pow_nonneg hr _)
  have hbq : b*q^p≤1 := by nlinarith [pow_nonneg hq p]
  linarith

end SphericalAging.GaussianOrthogonalForkCovariance
