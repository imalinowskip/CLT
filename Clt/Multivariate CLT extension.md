**Answer (Mathematical Explanation)**

A standard (and very common) way to construct a \(d\)-dimensional normal (Gaussian) distribution from univariate normals is via the following procedure:

1. **Start with i.i.d. standard normals**. Let \(Z = (Z_1, Z_2, \dots, Z_d)\) be a random vector whose coordinates \(Z_i\) are i.i.d. \(N(0,1)\) random variables (i.e., univariate normals).

2. **Apply a linear transform and a shift**.  Given a desired mean vector \(\mu \in \mathbb{R}^d\) and a desired covariance matrix \(\Sigma \in \mathbb{R}^{d \times d}\) (symmetric positive-definite), choose any matrix \(A\) such that
\[
   \Sigma \;=\; A A^\mathsf{T}.
\]
Then define
\[
   X \;=\; \mu \;+\; A Z.
\]
The random vector \(X\) has distribution \(\mathcal{N}(\mu, \Sigma)\).

3. **Measure-theoretic interpretation**.  
   - The law of \(Z\) is the *product measure* of \(d\) copies of the univariate standard Gaussian measure.
   - The law of \(X\) is the *pushforward* of that product measure through the affine map \(z \mapsto \mu + A z\).

Hence, if \(\gamma\) denotes the univariate standard normal measure on \(\mathbb{R}\), the \(d\)-dimensional standard normal measure on \(\mathbb{R}^d\) is \(\gamma^{\otimes d}\).  The measure of the multivariate normal \(\mathcal{N}(\mu, \Sigma)\) is
\[
   (\,\mu + A(\cdot)\,)_\#\bigl(\gamma^{\otimes d}\bigr),
\]
i.e., the image (pushforward) measure of \(\gamma^{\otimes d}\) under the map \(z \mapsto \mu + A z\).

---

**Part 1: Mathematical Explanation**

To prove the multivariate Central Limit Theorem (CLT) from a univariate CLT, a standard approach uses the *Cramér–Wold device*. We outline the key steps below.

---

### Setup

- Let \(X_1, X_2, \dots\) be i.i.d. random vectors in \(\mathbb{R}^d\) with
  \[
    \mathbb{E}[X_1] = \mu \quad \text{and} \quad 
    \mathrm{Cov}(X_1) = \Sigma,
  \]
  where \(\Sigma\) is a positive-semidefinite \(d \times d\) matrix.

- Define the sample mean of the first \(n\) vectors as
  \[
    \overline{X}_n = \frac{1}{n}\sum_{i=1}^{n} X_i.
  \]
  
- Then we look at the centered and scaled sum
  \[
    \sqrt{n} \Bigl(\overline{X}_n - \mu\Bigr) 
    \;=\; \frac{1}{\sqrt{n}} \sum_{i=1}^{n} (X_i - \mu).
  \]
  We want to show this converges in distribution to a multivariate normal with mean \(0\) and covariance \(\Sigma\):
  \[
    \sqrt{n}(\overline{X}_n - \mu) \xrightarrow{d} 
    \mathcal{N}\bigl(0,\,\Sigma\bigr).
  \]

---

### Cramér–Wold Device

The Cramér–Wold device says that a sequence of random vectors \(Y_n \in \mathbb{R}^d\) converges in distribution to a random vector \(Y\) if and only if for *every* \(t \in \mathbb{R}^d\), the scalar sequence \(t^\mathsf{T} Y_n\) converges in distribution to \(t^\mathsf{T} Y\).

1. **Project onto a univariate direction:**  
   Let 
   \[
     Y_n \;=\; \sqrt{n}\bigl(\overline{X}_n - \mu\bigr)
   \]
   and let \(t \in \mathbb{R}^d\). Then
   \[
     t^\mathsf{T} Y_n 
     \;=\; t^\mathsf{T} \bigl(\sqrt{n}(\overline{X}_n - \mu)\bigr)
     \;=\; \frac{1}{\sqrt{n}} \sum_{i=1}^{n} \bigl(t^\mathsf{T} (X_i - \mu)\bigr).
   \]
   Notice that \(t^\mathsf{T} (X_i - \mu)\) is now a *univariate* random variable.

2. **Apply the univariate CLT:**  
   By assumption, if we already have a proven (or assumed) univariate CLT in Lean, then the univariate random variables
   \[
     Z_i \;=\; t^\mathsf{T} (X_i - \mu)
   \]
   satisfy
   \[
     \frac{1}{\sqrt{n}} \sum_{i=1}^{n} Z_i 
     \;\xrightarrow{d}\; \mathcal{N}\!\bigl(0,\, \sigma_t^2\bigr),
   \]
   where \(\sigma_t^2 = \mathrm{Var}\bigl(t^\mathsf{T}(X_1 - \mu)\bigr) = t^\mathsf{T}\Sigma\,t\).  
   Hence,
   \[
     t^\mathsf{T} Y_n \;=\; \frac{1}{\sqrt{n}} \sum_{i=1}^{n} \bigl(t^\mathsf{T}(X_i-\mu)\bigr)
     \;\xrightarrow{d}\; \mathcal{N}\bigl(0,\,t^\mathsf{T}\Sigma\,t\bigr).
   \]

3. **Conclude multivariate convergence:**  
   Since this holds for *every* \(t \in \mathbb{R}^d\), the Cramér–Wold device tells us that
   \[
     Y_n \;=\; \sqrt{n}\bigl(\overline{X}_n - \mu\bigr)
     \;\xrightarrow{d}\; \mathcal{N}\bigl(0, \Sigma\bigr)
   \]
   as a random vector in \(\mathbb{R}^d\). This completes the multivariate CLT proof, assuming the univariate CLT is valid.

---

**Part 2: Lean Code Sketch**

Below is a **sketch** (rather than a polished library-ready file) of what the Lean formalization might look like. We assume there is already a Lean theorem called something like:

```lean
-- (Hypothetical) Univariate CLT in Lean
theorem univariate_CLT {X : ℕ → Ω → ℝ} (i.i.d. conditions...) :
  distribution (fun ω => (1 / real.sqrt n) * ∑ i in finset.range n, X i ω) 
    ⟶ normal_distribution(0, var(X))
```

We will then extend it to the multivariate case. 

<details>
<summary><strong>Lean code (click to expand)</strong></summary>

```lean
import measure_theory.probability_mass_function
import measure_theory.integration
import analysis.special_functions.exp_log
import data.real.sqrt
import topology.basic
import probability.probability_space
import probability.variance
import algebra.big_operators.basic

open_locale big_operators

namespace probability_theory

variables
  {Ω : Type*} [probability_space Ω]
  {d : ℕ}              -- dimension of the random vectors
  (X : ℕ → Ω → ℝ^d)    -- sequence of i.i.d. random vectors
  (μ : ℝ^d)            -- mean of each Xᵢ
  (Σ : matrix (fin d) (fin d) ℝ) -- covariance matrix of each Xᵢ

/-
  1) We assume each Xᵢ is i.i.d. with mean μ and covariance Σ.
  2) We rely on an existing univariate CLT, i.e., a statement that
     if we project Xᵢ onto a vector t ∈ ℝ^d, we get i.i.d. univariate random
     variables with mean tᵀμ and variance tᵀΣt.
-/
-- We'll need a lemma that states "projection of Xᵢ is i.i.d." or something similar.
lemma projection_iid (t : ℝ^d) :
  -- formal statement that tᵀ Xᵢ are i.i.d. real-valued random variables
  sorry := sorry

-- We'll need a lemma that states "E[tᵀ Xᵢ] = tᵀ μ, Var(tᵀ Xᵢ] = tᵀ Σ t".
lemma projection_mean (t : ℝ^d) : sorry := sorry
lemma projection_variance (t : ℝ^d) : sorry := sorry

/--
  **Multivariate Central Limit Theorem**: For i.i.d. random vectors `X_i : Ω → ℝ^d` 
  with mean `μ` and covariance `Σ`, the scaled sum converges in distribution 
  to the multivariate normal `Normal(0, Σ)`.
-/
theorem multivariate_CLT
  (hX_iid : i.i.d_sequence X)
  (hmean : ∀ i, ∫ (ω : Ω), X i ω ∂(prob_measure Ω) = μ)
  (hcov : ∀ i, compute_covariance (X i) = Σ)
  :
  -- statement that distribution of (1/√n) * Σᵢ (Xᵢ - μ) tends to Normal(0, Σ).
  -- In Lean, you might express "converges in distribution" using characteristic
  -- functions or some built-in notion (depending on your setup).
  converges_in_distribution
    (λ n, λ ω, (1 / real.sqrt n) • ∑ i in finset.range n, (X i ω - μ))
    (multivariate_normal_distribution 0 Σ)
:=
begin
  /- Proof sketch:
     1) For each t in ℝ^d, consider Yₙ(ω) = tᵀ[(1 / sqrt(n)) * Σ (Xᵢ(ω) - μ)].
     2) Apply univariate_CLT to the sequence tᵀ Xᵢ(ω).
     3) Conclude via Cramér–Wold that (1/sqrt(n)) * Σ (Xᵢ - μ) converges
        to Normal(0, Σ).
  -/
  apply cramer_wold,
  { -- For any t : ℝ^d, we consider the univariate random variables.
    intro t,
    -- Step 1: rewrite tᵀ(Yₙ) in terms of univariate sums
    have : (λ ω, t ⬝ ((1 / real.sqrt n) • ∑ i in finset.range n, (X i ω - μ)))
          = (λ ω, (1 / real.sqrt n) * ∑ i in finset.range n, (t ⬝ (X i ω - μ))),
    { ext ω,
      simp [matrix.dot_product, finset.sum_sub_distrib, sub_smul],
      -- Lean manipulations to show equivalence
    },
    -- Step 2: apply the univariate CLT to the sequence tᵀ Xᵢ(ω)
    specialize univariate_CLT (λ i ω, t ⬝ X i ω) ...,
    -- fill in i.i.d. assumptions, mean, variance, etc.
    -- We then get that (1/√n) * Σᵢ tᵀ(Xᵢ - μ) converges to N(0, tᵀΣt).
    -- Step 3: The Cramér–Wold device yields the desired multivariate limit.
    sorry
  }
end

end probability_theory
```

</details>

#### Explanation of the Lean sketch

1. **Imports / Setup**: We import various Lean libraries related to probability, integrals, etc.  
2. **Namespace and variables**:
   - \(\Omega\) is the underlying probability space.  
   - \(d\) is the dimension.  
   - `X : ℕ → Ω → ℝ^d` is a family of i.i.d. random vectors.  
   - `μ : ℝ^d` is the mean of each \(X_i\).  
   - `Σ : matrix (fin d) (fin d) ℝ` is the covariance matrix.  

3. **Auxiliary lemmas**:
   - `projection_iid t`: states that \(t^\mathsf{T} X_i\) (a scalar) is i.i.d.  
   - `projection_mean t`: states that \( \mathbb{E}[t^\mathsf{T} X_i] = t^\mathsf{T} μ\).  
   - `projection_variance t`: states that \(\mathrm{Var}[t^\mathsf{T} X_i] = t^\mathsf{T} \Sigma\, t\).  

4. **The statement**: `multivariate_CLT` states that
   \[
     \frac{1}{\sqrt{n}} \sum_{i=1}^{n} \bigl(X_i(\omega) - \mu\bigr)
     \;\xrightarrow{d}\;
     \text{MultivariateNormal}\bigl(0,\Sigma\bigr).
   \]

5. **Proof strategy**:
   - We invoke a Lean version of the Cramér–Wold device (`cramer_wold`), which likely requires checking that for each \(t\), \(t^\mathsf{T}(\text{the scaled sum})\) converges in distribution to \(t^\mathsf{T} \mathcal{N}(0,\Sigma) = \mathcal{N}(0, t^\mathsf{T}\Sigma t)\).  
   - We use `univariate_CLT` on the sequence \(t^\mathsf{T} X_i\).  
   - The rest is finished by the Cramér–Wold argument.

This code is only *indicative*: in a real Lean development, you would have the relevant lemmas, definitions (`cramer_wold`, `univariate_CLT`) fully stated and proved, plus a notion of “converges in distribution” that is recognized by Lean. The main takeaway is **how** the univariate CLT is lifted to the multivariate case via the projection trick (Cramér–Wold).

---

### Summary

1. **Mathematically**, you apply the univariate CLT in each direction \(t \in \mathbb{R}^d\).  
2. **Formally in Lean**, you:
   - State a lemma that for each \(t\), \(t^\mathsf{T} X_i\) is i.i.d. univariate with mean \(t^\mathsf{T}\mu\) and variance \(t^\mathsf{T}\Sigma t\).  
   - Apply the univariate CLT to conclude \(t^\mathsf{T}\bigl(\sqrt{n}(\overline{X}_n - \mu)\bigr)\) converges to \(\mathcal{N}(0, t^\mathsf{T}\Sigma t)\).  
   - Use the Cramér–Wold device to upgrade to the statement that \(\sqrt{n}(\overline{X}_n - \mu)\) converges to \(\mathcal{N}(0, \Sigma)\) in \(\mathbb{R}^d\).  

Thus, if you already have a univariate CLT proved in Lean, the extension to the multivariate CLT requires essentially adding the Cramér–Wold argument plus some straightforward lemmas about projecting vectors onto a given direction.