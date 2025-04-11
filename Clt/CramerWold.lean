import Clt.CharFun

noncomputable section

open Mathlib MeasureTheory ProbabilityTheory Topology Filter Vector Complex Isometry BoundedContinuousFunction Finset

open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
variable {P : ProbabilityMeasure Ω}
variable {d : ℕ+}
variable {X : Ω → Fin d → ℝ}
variable {Xn : ℕ → Ω → Fin d → ℝ}

#check dotProduct

def dotProduct_RV {Ω} (t : Fin d → ℝ) (X : Ω → Fin d → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin d, t i * X ω i

def dotProduct_RV' {Ω} (t : Fin d → ℝ) (X : Ω → Fin d → ℝ) (ω : Ω) : ℝ :=
  dotProduct t (X ω)

def dotProduct_fixed (t : Fin d → ℝ) (x : Ω → Fin d → ℝ) : Ω → ℝ :=
  fun ω => @dotProduct_RV d Ω t x ω

noncomputable instance : Inner ℝ (Fin d → ℝ) where
  inner x y := ∑ i, x i * y i

lemma measurable_dotProduct (t : Fin d → ℝ) (hX : Measurable X) :
  Measurable (dotProduct_RV t X) :=
  by
    apply Finset.measurable_sum
    intros i _
    let Xi := fun ω => X ω i
    have hXi : Measurable Xi := (measurable_pi_apply i).comp hX
    exact Measurable.const_mul hXi (t i)

lemma measurable_dotProduct_shorter (t : Fin d → ℝ) (hX : Measurable X) :
  Measurable (dotProduct_RV t X) :=
  Finset.measurable_sum _ (fun i _ => Measurable.const_mul ((measurable_pi_apply i).comp hX) (t i))

lemma aemeasurable_dotProduct {μ : Measure Ω} (t : Fin d → ℝ) (hX : Measurable X) :
  AEMeasurable (dotProduct_RV t X) μ :=
  (measurable_dotProduct_shorter t hX).aemeasurable

/-theorem measure_tendsto_if_charFun_tendsto (μ : ProbabilityMeasure (Fin d → ℝ)) (μs : ℕ → ProbabilityMeasure (Fin d → ℝ)) :
  (∀ t, Tendsto (fun i ↦ charFun (μs i) t) atTop (𝓝 (charFun (μ : Measure (Fin d → ℝ)) t))) → Tendsto μs atTop (𝓝 μ)
  := sorry-/

/-lemma tendsto_integral_of_weakConv
  (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
  {f : BoundedContinuousFunction (Fin d → ℝ) ℂ} :
  Tendsto (fun n => ∫ x, f x ∂(P.map (hXn n).aemeasurable)) atTop (𝓝 (∫ x, f x ∂(P.map hX.aemeasurable)))
  := sorry-/

--lemma abs_exp_ofReal_mul_I (u : ℝ) : Complex.abs (Complex.exp (u * Complex.I)) = 1 :=
--  by simp [Complex.abs_exp_ofReal_mul_I]

lemma continuous_exp_ofReal_mul_I : Continuous (fun u : ℝ => Complex.exp (u * Complex.I))
  := continuous_exp.comp (Continuous.mul continuous_ofReal continuous_const)

lemma complex_dist_zero_eq_abs (z : ℂ) : dist z 0 = ‖z‖ :=
calc
  dist z 0 = ‖z - 0‖ := rfl
  _ = ‖z‖ := by rw [sub_zero]

lemma complex_dist_zero_eq_abs' (z : ℂ) : dist 0 z = ‖z‖ :=
by rw [dist_comm, complex_dist_zero_eq_abs z]

lemma cexp_bound_exact : ∀ (u v : ℝ), dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I)) ≤ 2 :=
  fun u v =>
    calc
      dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I))
        ≤ dist (Complex.exp (↑u * I)) 0 + dist 0 (Complex.exp (↑v * I)) := dist_triangle _ _ _
      _ = ‖Complex.exp (↑u * I)‖ + ‖Complex.exp (↑v * I)‖ := by rw [complex_dist_zero_eq_abs, complex_dist_zero_eq_abs']
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

def bounded_continuous_exp_ofReal_mul_I : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun u => Complex.exp (u * Complex.I), continuous_exp_ofReal_mul_I⟩ 2 cexp_bound_exact

/-
lemma dot_product_lipschitz2 (t : Fin d → ℝ) :
  LipschitzWith (∑ i, |t i|).toNNReal (fun x : Fin d → ℝ => ∑ i, t i * x i) :=
by
  intros x y
  have h1 : (∑ i, t i * x i) - (∑ i, t i * y i) = ∑ i, t i * (x i - y i) :=
    by
      rw [Finset.sum_congr rfl (fun i hi => mul_sub (t i) (x i) (y i))]
      rw [←Finset.sum_sub_distrib]
  rw [edist_dist, Real.dist_eq, h1]

  have h2 : |∑ i, t i * (x i - y i)| ≤ (∑ i, |t i|) * (edist x y).toReal :=
  by calc
    |∑ i, t i * (x i - y i)| ≤ ∑ i, |t i * (x i - y i)| :=
      abs_sum_le_sum_abs (fun i => t i * (x i - y i)) (Finset.univ : Finset (Fin d))
    _ = ∑ i, |t i| * |x i - y i| :=
      by rw [Finset.sum_congr rfl (fun i hi => by rw [abs_mul])]
    _ ≤ (∑ i, |t i| * (Finset.univ.sup' Finset.univ_nonempty (fun j => |x j - y j|))) :=
      Finset.sum_le_sum fun i hi => by
        apply mul_le_mul_of_nonneg_left
        · refine (Real.toNNReal_le_toNNReal_iff ?_).mp ?_
          · rcases Finset.univ_nonempty with ⟨k, hk⟩
            apply le_trans (abs_nonneg (x k - y k)) (Finset.le_sup' (fun j => |x j - y j|) hk)
          · exact Real.toNNReal_mono (Finset.le_sup' (fun j : Fin d => |x j - y j|) (Finset.mem_univ i))
        · exact abs_nonneg (t i)
    _ ≤ (∑ i, |t i|) * (Finset.univ.sup' Finset.univ_nonempty (fun j => |x j - y j|)) := by rw [sum_mul]
    _ ≤ (∑ i, |t i|) * (edist x y).toReal := by sorry

  calc
    ENNReal.ofReal |∑ i, t i * (x i - y i)|
      ≤ ENNReal.ofReal ((∑ i, |t i|) * (edist x y).toReal) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (∑ i, |t i|) * ENNReal.ofReal  (edist x y).toReal :=
        by rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun i _ => abs_nonneg (t i)))]
    _ ≤ ENNReal.ofReal (∑ i, |t i|) * (edist x y) := by
        apply mul_le_mul_of_nonneg_left (ENNReal.ofReal_toReal_le) (zero_le _)
    _ = (∑ i, |t i|).toNNReal * edist x y :=
        by rw [ENNReal.ofNNReal_toNNReal]


lemma dot_product_lipschitz (t : Fin d → ℝ) :
  LipschitzWith (∑ i, |t i|).toNNReal (fun x : Fin d → ℝ => ∑ i, t i * x i) :=
by
  intros x y
  rw [edist_eq]
  have h :
    (∑ i : Fin d, t i * x i) - (∑ i : Fin d, t i * y i) = (∑ i : Fin d, (t i * x i - t i * y i))
    := by rw [Finset.sum_sub_distrib]
  have h2 :
    ∑ i : Fin d, t i * (x i - y i) = ∑ i : Fin d, (t i * x i - t i * y i)
    := Finset.sum_congr rfl (fun i hi => mul_sub (t i) (x i) (y i))
  have h3 :
    (∑ i : Fin d, t i * x i) - (∑ i : Fin d, t i * y i) = (∑ i : Fin d, (t i * (x i - y i)))
    := by rw [h, h2.symm]
  have eq_abs :
    |(∑ i : Fin d, t i * x i) - (∑ i : Fin d, t i * y i)| = |∑ i : Fin d, t i * (x i - y i)|
    := by rw [congrArg (fun z : ℝ => |z|) h3]
  have h_tri :
    |∑ i : Fin d, t i * (x i - y i)| ≤ ∑ i in (univ : Finset (Fin d)), |t i * (x i - y i)|
    := abs_sum_le_sum_abs (fun i => t i * (x i - y i)) univ
  have h_abs_mul :
    ∑ i in (univ : Finset (Fin d)), |t i * (x i - y i)| = ∑ i in (univ : Finset (Fin d)), |t i| * |x i - y i|
    := Finset.sum_congr rfl (fun i hi => by rw [abs_mul])
  have h_nonempty : (univ : Finset (Fin d)).Nonempty := ⟨(0 : Fin d), by simp⟩
  let M := (univ : Finset (Fin d)).sup' h_nonempty (fun i => |x i - y i|)
  have h_bound : ∀ i ∈ (univ : Finset (Fin d)), |x i - y i| ≤ M :=
  fun i hi => Finset.sup'_mem (univ : Finset (Fin d)) (fun j => |x j - y j|) h_nonempty i hi
-/

def bounded_continuous_exp_inner_mul_I (t : Fin d → ℝ) : (Fin d → ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.compContinuous bounded_continuous_exp_ofReal_mul_I ⟨(fun x : (Fin d → ℝ) => ∑ i : Fin d, t i * x i),
    by
      apply continuous_finset_sum
      intros i hi
      continuity⟩

lemma inner_R_eq_mul (s y : ℝ) : inner s y = s * y :=
  by
    simp [inner]
    simp [mul_comm]

#check @ProbabilityMeasure.tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop
-- @ProbabilityMeasure.tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop  μₙ μ f hconv_t

@[simp] lemma bounded_continuous_exp_ofReal_mul_I_eq_cexp (u : ℝ) :
  bounded_continuous_exp_ofReal_mul_I u = Complex.exp (u * Complex.I) :=
rfl

lemma charFun_tendsto_if_inner_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : Fin d → ℝ, Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct t (hXn n))) atTop (𝓝 (P.map (aemeasurable_dotProduct t hX)))) → (∀ t : Fin d → ℝ, Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (P.map hX.aemeasurable) t))) :=
  by
    intros hconv t
    let φ := bounded_continuous_exp_inner_mul_I t

    have h_eq3 : charFun (P.map hX.aemeasurable) t = ∫ x, Complex.exp ((dotProduct_RV t X) x * Complex.I) ∂P :=
      by
        simp only [charFun]
        apply MeasureTheory.integral_map
        · exact hX.aemeasurable
        · exact φ.continuous.stronglyMeasurable.aestronglyMeasurable
    have h_eq_final : charFun (P.map hX.aemeasurable) t = ∫ x, Complex.exp (x * Complex.I) ∂(P.map (aemeasurable_dotProduct t hX)).toMeasure :=
      by
        rw [h_eq3]
        rw [eq_comm]
        apply MeasureTheory.integral_map
        · exact (aemeasurable_dotProduct t hX)
        · exact continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable

    have h_eq_n : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, φ (Xn n x) ∂P := by
      intro n
      simp only [charFun]
      apply MeasureTheory.integral_map
      · exact (hXn n).aemeasurable
      · exact φ.continuous.stronglyMeasurable.aestronglyMeasurable
    have h_eq_n_final : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, Complex.exp (x * Complex.I) ∂(P.map (aemeasurable_dotProduct t (hXn n))).toMeasure :=
      by
        intro n
        rw [h_eq_n]
        rw [eq_comm]
        apply MeasureTheory.integral_map
        · exact (aemeasurable_dotProduct t (hXn n))
        · exact continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable

    let ψ := bounded_continuous_exp_ofReal_mul_I
    let ψ_re := (fun u => (ψ u).re)
    let ψ_im := (fun u => (ψ u).im)

    let ψ_re_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_re u) (ψ_re v) ≤ 2 := fun u v =>
    calc
      dist (ψ_re u) (ψ_re v)
        ≤ dist (ψ_re u) 0 + dist 0 (ψ_re v) := dist_triangle _ _ _
      _ = |ψ_re u| + |ψ_re v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_re u‖ + ‖ψ_re v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_re_le_norm (ψ u)) (RCLike.norm_re_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num
    let ψ_im_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_im u) (ψ_im v) ≤ 2 := fun u v =>
    calc
      dist (ψ_im u) (ψ_im v)
        ≤ dist (ψ_im u) 0 + dist 0 (ψ_im v) := dist_triangle _ _ _
      _ = |ψ_im u| + |ψ_im v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_im u‖ + ‖ψ_im v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_im_le_norm (ψ u)) (RCLike.norm_im_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

    let ψ_re_bcf : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨ψ_re, Continuous.comp continuous_re ψ.continuous⟩ 2 ψ_re_bcf_bound_exact
    let ψ_im_bcf : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨ψ_im, Continuous.comp continuous_im ψ.continuous⟩ 2 ψ_im_bcf_bound_exact

    let ψ_decomp (x : ℝ) : ψ x = ψ_re_bcf x + (ψ_im_bcf x) * Complex.I :=
      by
        simp [ψ_re_bcf, ψ_im_bcf]
        rw [Complex.re_add_im]

    let h_lim (f : ℝ →ᵇ ℝ) : 0 ≤ f → atTop.limsup (fun n => ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n))))) ≤ ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct t hX))) :=
      by
        intro f_nn
        let μₙ : ℕ → ProbabilityMeasure ℝ :=
          fun n => (P.map (aemeasurable_dotProduct t (hXn n)) : ProbabilityMeasure ℝ)
        let μ : ProbabilityMeasure ℝ :=
          (P.map (aemeasurable_dotProduct t hX) : ProbabilityMeasure ℝ)
        let hconv_t : Tendsto μₙ atTop (𝓝 μ)
          := hconv t
        have hf : Tendsto (fun n => ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n))))) atTop
                        (𝓝 (∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct t hX))))) :=
          by
            have h_iff := @ProbabilityMeasure.tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop μₙ μ
            have h_rhs := Iff.mp h_iff hconv_t
            exact h_rhs f

        exact le_of_eq (Tendsto.limsup_eq hf)

    have integralConv_re :
      Tendsto (fun n => ∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n))))) atTop (𝓝 (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t hX))))) := BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_re_bcf

    have integralConv_im :
      Tendsto (fun n => ∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n))))) atTop (𝓝 (∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t hX)))) ) :=
      BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_im_bcf

    have h_mul_one : ∀ x, x * Complex.ofReal 1 = x := by simp

    have h_integral_smul_const_ψ_re_bcf : ∀ (ν : Measure ℝ), ∫ x, ψ_re_bcf x * Complex.ofReal 1 ∂ ν = (∫ x, ψ_re_bcf x ∂ ν) * Complex.ofReal 1 :=
    by
      intro ν
      exact integral_smul_const ψ_re_bcf (Complex.ofReal 1)
    have h_integral_smul_const_ψ_im_bcf : ∀ (ν : Measure ℝ), ∫ x, ψ_im_bcf x * Complex.I ∂ ν = (∫ x, ψ_im_bcf x ∂ ν) * Complex.I :=
    by
      intro ν
      exact integral_smul_const ψ_im_bcf (Complex.I)

    have h_ψ : ∀ (ν : ProbabilityMeasure ℝ), ∫ x, ψ x ∂ ν = ∫ x, ψ_re_bcf x ∂ ν + (∫ x, ψ_im_bcf x ∂ ν) * Complex.I :=
      by
        intro ν
        have h : ∀ x, ψ x = (ψ_re_bcf x) * Complex.ofReal 1 + (ψ_im_bcf x) * Complex.I := by
          intro x
          rw [h_mul_one]
          exact ψ_decomp x
        rw [integral_congr_ae (Eventually.of_forall h), integral_add]

        rw [h_integral_smul_const_ψ_re_bcf ν]
        rw [h_integral_smul_const_ψ_im_bcf ν]
        rw [h_mul_one]

        simp [h_mul_one]

        have h_ψ_re_bcf_integ : Integrable ψ_re_bcf ν := BoundedContinuousFunction.integrable ν ψ_re_bcf
        have h_c_ψ_re_bcf_integ : Integrable (fun a => (ψ_re_bcf a : ℂ)) ↑ν := by exact h_ψ_re_bcf_integ.ofReal
        exact h_c_ψ_re_bcf_integ

        have h_ψ_im_bcf_integ : Integrable ψ_im_bcf ν := BoundedContinuousFunction.integrable ν ψ_im_bcf
        have h_c_ψ_im_bcf_integ : Integrable (fun a => (ψ_im_bcf a : ℂ)) ↑ν := by exact h_ψ_im_bcf_integ.ofReal

        exact h_ψ_im_bcf_integ.ofReal.mul_const Complex.I

    have integralConv :
      Tendsto (fun n => ∫ (x : ℝ), ψ x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n))))) atTop (𝓝 (∫ (x : ℝ), ψ x ∂ (↑(P.map (aemeasurable_dotProduct t hX))))) :=
        by
          rw [h_ψ]
          have h1 : Tendsto (fun n => Complex.ofReal (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n)))))) atTop
            (𝓝 (↑(∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t hX)))))) :=
            Tendsto.ofReal integralConv_re
          have h2 : Tendsto (fun n => Complex.ofReal (∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t (hXn n)))))) atTop
            (𝓝 (↑(∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct t hX)))))) :=
            Tendsto.ofReal integralConv_im
          have h3 := Tendsto.mul h2 (tendsto_const_nhds : Tendsto (fun _ => Complex.I) atTop (𝓝 Complex.I))
          have h4 := Tendsto.add h1 h3

          have : ∀ n, ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct t (hXn n)))) =
                        ∫ x, ψ_re_bcf x ∂(↑(P.map (aemeasurable_dotProduct t (hXn n)))) +
                        (∫ x, ψ_im_bcf x ∂(↑(P.map (aemeasurable_dotProduct t (hXn n))))) * Complex.I :=
            fun n => h_ψ _
          refine Tendsto.congr' ?_ h4
          simp_rw [this]
          simp [EventuallyEq.of_eq]

    rw [h_eq_final]

    have h_char_eq_n : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct t (hXn n)))) :=
      fun n => h_eq_n_final n ▸ rfl

    have h_char_eq_lim : charFun (P.map hX.aemeasurable) t = ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct t hX))) :=
      h_eq_final

    simp_rw [h_char_eq_n]

    have hψ_eq_cexp : (fun x : ℝ => ψ x) = (fun x : ℝ => Complex.exp (x * Complex.I)) := by
      ext x
      rfl

    have h_lim_eq : ∫ x, Complex.exp (x * Complex.I) ∂((P.map (aemeasurable_dotProduct t hX)).toMeasure) =
                ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct t hX))) :=
      by rw [← hψ_eq_cexp]

    rw [h_lim_eq]
    exact integralConv

#check UpperSemicontinuous.limsup_le

theorem rv_tendsto_if_charFun_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : Fin d → ℝ, Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (P.map hX.aemeasurable) t))) → Tendsto (fun n ↦ P.map (hXn n).aemeasurable) atTop (𝓝 (P.map hX.aemeasurable))
  := sorry

theorem cramerWold (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)) :
  (∀ t : Fin d → ℝ, Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct t (hXn n))) atTop (𝓝 (P.map (aemeasurable_dotProduct t hX)))) → (Tendsto (fun n : ℕ => P.map (hXn n).aemeasurable) atTop (𝓝 (P.map hX.aemeasurable)))
  := by
  intro h
  exact (rv_tendsto_if_charFun_tendsto hX hXn) ((charFun_tendsto_if_inner_tendsto hX hXn) (h))

#min_imports
