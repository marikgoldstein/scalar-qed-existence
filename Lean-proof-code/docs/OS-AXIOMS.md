# The Osterwalder–Schrader axioms OS0, OS1 without rotations, OS2, OS3

Theorem `GGOS.osterwalder_schrader` ([Statement](../GGOS/OS/Statement.lean)), after [GG-OS] Section 9. Definitions: [Motion](../GGOS/Infra/Motion.lean) (Euclidean motions with linear part in the cubic group, plane reflections), [Schwinger](../GGOS/OS/Schwinger.lean) (generating function, Schwinger functions, weighted norm), [LimitFunctionalDef](../GGOS/OS/LimitFunctionalDef.lean), [Axioms](../GGOS/OS/Axioms.lean) (the four axioms). Proofs: [GGOS/OS/Work](../GGOS/OS/Work/). Axioms used: `propext`, `Classical.choice`, `Quot.sound`.

## What the theorem says

Fix `a_0 > 0` and a bounded Borel density function `g_d`. There is a constant `C` such that the following holds for every start level, every sequence of coefficient records (Remark 2.1) and every sequence of states `ω_N` that are limit points of the torus states (Definition 2.3).

1. Limit functionals exist (given the limit points): there are levels `N_m → ∞` and a linear functional `S` on `ℂ[𝒯]` with `S(a) = lim_m ω_{N_m}(ι_{N_m}(a))`.
2. Every such `S` satisfies:
   - **OS0** (from Theorem 9.4): `S(1) = 1`; `|S(e_σ) − S(e_τ)| ≤ ‖σ − τ‖`; the generating function of every finite family extends to an entire function `Ψ` with `|Ψ(z)| ≤ Ψ(Re z)` and the Gaussian bound; `|S_n(σ_1,…,σ_n)| ≤ e^n (n!)^{1/2} ∏‖σ_i‖`; the same with `C^n` and the weighted sup norm (condition (E0′) in product form); `S_2(f,f) ≤ R(f)²`.
   - **OS1 without rotations** (Proposition 9.6): invariance under all translations, the reflections in the coordinate planes and the cubic group about every point, for `S` and for the Schwinger functions.
   - **OS2** (Propositions 9.9, 9.11) for the reflection in every plane `{x_j = c}`: `S(Θa) = conj S(a)`, the form `S(Θa·b)` is Hermitian, and positive semidefinite on the algebra of the open half space; positivity for polynomials of the field.
   - **OS3** (Proposition 9.12): the Schwinger functions are symmetric, multilinear and real on real test pairs; charge conjugation; the odd curvature functions vanish.
   - The correlation functions of the limit points converge to the Schwinger functions.

## Deviations from [GG-OS]

1. **Joint field.** Theorem 9.4 (ii), (iii), Propositions 9.11 and 9.12 (a) are printed for the curvature; they are stated here for the joint field of the curvature and of the bounded density function, with `‖(f,h)‖ = R(f) + ‖g_d‖_∞ E(h)`. For `h = 0` the printed bounds in the norm `R(f)` are recovered with the printed constants (the constant of (E0′) is the one of deviation 3).
2. **Test functions.** Real `C_c^∞` test pairs. The bound (E0′) is stated in product form on them; the extension to Schwartz functions, complex test functions and the statement "tempered distribution" are not formalized.
3. **Constants.** The constant of (E0′) depends on `a_0` and `g_d` only; it is an integral of `(1 + ‖x‖_∞²)^{-2}` instead of the explicit `π²(2 + (3/2)a_0²)²` of Lemma 9.1.
4. **Limit points.** Any even sides and any coefficients are allowed, as in `GGOS.limit_functional`. That limit points exist ([GG-OS] Theorem 11.5) is not formalized; it is the hypothesis of the theorem.
5. **Theorem 9.7, Corollary 9.8.** Reflection positivity is proved at the site planes (`c = 0`), for the variables of the closed half and in the `L²` form; the bond mid-planes `c = ε_N/2` are not needed and not formalized. The weight is written as a half weight times its reflection (the factors of the plane with exponent one half) instead of three groups of factors.
6. **Lemma 9.3, Theorem 9.4.** The limit laws are obtained from Lévy's and Prokhorov's theorems instead of Montel's theorem; the Schwinger functions are defined as mixed derivatives of the generating function at 0 and proved to be the moments of the limit laws; the growth bound uses `t^n/n! ≤ cosh t` and the inequality of the means instead of Cauchy's estimate.
7. **Not formalized from Section 9.1–9.4.** Lemma 9.2 and `0 ≤ Z(f,0) ≤ 1`; Lemma 9.3 (a), (b) (the generating functions on the torus and at level N); the bound of Z by the weighted norm and its extension to Schwartz functions in Theorem 9.4 (i); Theorem 9.10 (matrix form at complex arguments); the torus part of Theorem 9.4 (iv); `S_n(f̄) = conj S_n(f)` for complex test functions. Rotations, the measure (Theorem 9.13) and OS4 are outside the scope.

## The full statement

`GGOS.osterwalder_schrader_full` ([FullStatement](../GGOS/OS/FullStatement.lean)) adds two clauses to the theorem above, both stated with `sorry` in [Open](../GGOS/OS/Open.lean):

- **OS0 on Schwartz test functions** ([GG-OS] Theorem 9.4 (i), (iii), for the curvature): the generating functional extends to a continuous function on real Schwartz 2-forms, and each curvature Schwinger function extends to a continuous multilinear form on them with the bound (E0′) and the same constant (`GGOS.OS0Schwartz`, [Schwartz](../GGOS/OS/Schwartz.lean)). It is stated as a consequence of OS0 and OS3 on smooth compactly supported test pairs (`GGOS.OS.os0Schwartz_of`).
- **OS1 with rotations** ([GG-OS] Theorem 12.4, with Theorems 12.2 and 12.3): when the limit points run along dyadic sequences of sides (Definition 14.1, `GGOS.IsDyadicLimitPoint`) and the hopping coefficients are positive at every level, every limit functional is invariant under the transport of test pairs by O(3) (Definition 12.7, `GGOS.rotT`, [Rotation](../GGOS/OS/Rotation.lean)); with the translations of OS1 without rotations this is invariance under the whole Euclidean group (`GGOS.OS1`). The rotation part is `GGOS.OS.rotation_invariance`; the step from it to `GGOS.OS1` is proved.

OS4 is not stated: [GG-OS] proves it in a weak form, for the ergodic components of the measure of its Theorem 9.13 (Theorem 9.15), and neither the measure nor an ergodic decomposition is formalized here.
