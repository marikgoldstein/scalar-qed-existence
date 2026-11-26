# HiggsOS

HiggsOS is a Lean 4 proof that the three-dimensional lattice abelian Higgs model (scalar QED₃) has a continuum limit, along a subsequence of lattice spacings, that satisfies the Osterwalder–Schrader axioms OS0, OS1 without rotations, OS2 and OS3. It formalizes results of

> M. Goldstein, A. Guevara, *Osterwalder–Schrader axioms for scalar QED₃ in the Higgs phase*, hexagon:2611.00321v1 (cited below as [GG-OS]).

The main theorem is proved without `sorry` and depends only on `propext`, `Classical.choice` and `Quot.sound`. A second theorem states the axioms as far as [GG-OS] proves them, with `sorry` exactly where the Lean proof is missing (see below).

## The model

The lattice has spacing ε_N = a₀ 5^{−N} and is periodic (a torus). In unitary gauge the variables are the modulus ρ_x = ρ₀,₀ + ρ̃_x ≥ 0 of the scalar field on sites, an angle B_b ∈ (−π/γ, π/γ] on bonds (γ the lattice charge), and Villain integers m_p on plaquettes with dm = 0 (no monopoles). With the curvature 𝔣_p = (dB)_p + (2π/γ) m_p, the weight is

$$W=\prod_x \rho_x\, e^{-\lambda_0(\rho_x^2-\rho_{0,0}^2)^2-\delta m_B\,\rho_x^2/2}\ \prod_{b=(x,y)} e^{-\frac{\kappa}{2}\left|e^{i\gamma B_b}\rho_y-\rho_x\right|^2}\ \prod_p e^{-\mathfrak f_p^2/2}.$$

All theorems hold for any γ, λ₀, ρ₀,₀ > 0, κ ≥ 0 and real δm_B, which may change with the spacing; the coupling values of [GG-OS] Section 2 are one choice among them.

## The continuum limit

The observables are the curvature and a bounded function g_d of the density, smeared with a test pair σ = (f, h) of smooth compactly supported functions (f a 2-form):

$$\Phi_N(\sigma)=\varepsilon_N^{3/2}\sum_p f_{\mu\nu(p)}(x_p)\,\mathfrak f_p+\varepsilon_N^{3}\sum_z h(z)\,g_d(\tilde\rho_z).$$

At each spacing, ω_N is a limit point of the torus states as the torus grows. Along a sequence of levels N_m → ∞ the generating functionals converge for every test pair,

$$S(e_\sigma)=\lim_{m\to\infty}\omega_{N_m}\!\left(e^{i\Phi_{N_m}(\sigma)}\right),$$

and S, extended linearly to finite combinations of the e_σ, is a limit functional. Its Schwinger functions are the moments of the limit field.

## What is proved

For every limit functional:

- **OS0.** |S_n(σ₁, …, σ_n)| ≤ Cⁿ (n!)^{1/2} ∏ |σ_i| for smooth compactly supported test pairs, with |σ| = sup_x (1 + |x|²)² max(|f(x)|, |h(x)|) and C depending only on a₀ and g_d. The generating functions of finite families are entire with Gaussian bounds, and S(e_σ) is 1-Lipschitz in the L² norm of f plus ‖g_d‖_∞ times the L¹ norm of h. The extension to Schwartz test functions is stated with `sorry` ([GG-OS] Theorem 9.4).
- **OS1 without rotations.** Invariance under all translations, the reflections in coordinate planes, and the 48 symmetries of the cube about every point. Invariance under the whole Euclidean group is stated with `sorry`, for limit points along dyadic sequences of sides with positive hopping coefficients ([GG-OS] Theorem 12.4).
- **OS2.** Reflection positivity for the reflection in every coordinate plane {x_j = c}, also for polynomials of the smeared field.
- **OS3.** The Schwinger functions are symmetric, multilinear and real; S is invariant under charge conjugation, and the odd curvature functions vanish.
- **OS4** is not stated in Lean. [GG-OS] proves it in a weak form, for the ergodic components of the measure of its Theorem 9.13 (Theorem 9.15).

The lattice correlation functions of ω_{N_m} converge to the Schwinger functions.

## Hypotheses and open points

- The states ω_N are assumed to be limit points of the torus states at every level N ≥ N₀; their existence ([GG-OS] Theorem 11.5) is not formalized. Given them, a limit functional exists.
- Different sequences of levels may give different limit functionals; uniqueness is not claimed.
- Stated with `sorry`: the extension to Schwartz test functions and the rotation invariance. Not formalized: OS4, the measure on distributions ([GG-OS] Theorem 9.13), complex test functions, and the non-triviality of the limit.

## How the proof goes

1. **Gaussian domination** ([GG-OS] Theorem 3.1): on every torus, for all couplings, the expectation of exp(Σ_p a_p 𝔣_p) is at most exp(½ Σ_p a_p²). The proof completes the square in the Villain weight, sums over m by Poisson's formula and uses the nonnegative Fourier coefficients of the hopping factor.
2. **A uniform bound** ([GG-OS] Definition 4.1, Proposition 4.2): ω_N(min(|Φ_N(σ)|, 2)) ≤ ‖σ‖ uniformly in N, for the norm ‖σ‖ of OS0.
3. **Compactness** ([GG-OS] Proposition 6.1, Theorem 7.1): the generating functionals are bounded by 1 and uniformly continuous in ‖σ‖, so a subsequence converges.
4. **Symmetry and positivity** ([GG-OS] Lemma 5.1, Section 9): the lattice symmetries and reflection positivity at the site planes pass from the torus states to the limit, where the meshes ε_N ℤ³ become dense.
5. **Moments** ([GG-OS] Section 9): the bound of step 1 controls all moments uniformly in N, which gives OS0 and OS3.

## The Lean statements

| Result | Lean theorem | File |
|---|---|---|
| OS0, OS1 without rotations, OS2, OS3 ([GG-OS] Section 9) | `GGOS.osterwalder_schrader` | `GGOS/OS/Statement.lean` |
| The same, plus OS0 on Schwartz test functions and OS1 with rotations, the last two with `sorry` ([GG-OS] Theorems 9.4, 12.4) | `GGOS.osterwalder_schrader_full` | `GGOS/OS/FullStatement.lean` |
| Gaussian domination ([GG-OS] Theorem 3.1, first sentence) | `GGOS.gaussian_domination` | `GGOS/Frozen/GaussianDomination.lean` |
| Moments ([GG-OS] Theorem 3.1, second sentence) | `GGOS.gaussian_moments` | `GGOS/Frozen/GaussianMoments.lean` |
| The norm of test pairs ([GG-OS] Definition 4.1) | `GGOS.pairNorm_finite_seminorm_admissible` | `GGOS/Frozen/PairNorm.lean` |
| Torus estimate ([GG-OS] Proposition 4.2) | `GGOS.torus_estimate` | `GGOS/Frozen/TorusEstimate.lean` |
| Torus symmetry ([GG-OS] Lemma 5.1) | `GGOS.torus_symmetry` | `GGOS/Frozen/TorusSymmetry.lean` |
| Passage to the limit ([GG-OS] Proposition 6.1) | `GGOS.passage_to_limit` | `GGOS/Frozen/PassageToLimit.lean` |
| The limit functional ([GG-OS] Theorem 7.1) | `GGOS.limit_functional` | `GGOS/Frozen/LimitFunctional.lean` |

The axioms are Lean structures in `GGOS/OS/Axioms.lean`, `GGOS/OS/Schwartz.lean` and `GGOS/OS/Rotation.lean`; the two statements with `sorry` are in `GGOS/OS/Open.lean`; the definitions are in `GGOS/Frozen/Defs` and `GGOS/Infra`, one per file; the proofs are in `GGOS/Providers`, `GGOS/Work` and `GGOS/OS/Work`. Differences from the printed text (scope, conventions, other proof routes) are listed in [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) and [docs/OS-AXIOMS.md](docs/OS-AXIOMS.md). No erratum in [GG-OS] was found.

## Building and checking

Lean `leanprover/lean4:v4.34.0-rc2` (see `lean-toolchain`), Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` (see `lakefile.toml` and `lake-manifest.json`).

```bash
lake exe cache get                                  # download the Mathlib build cache
lake build                                          # build the library GGOS
lake env lean scripts/PrintAxiomsOS.lean            # axioms of the OS theorem
lake env lean scripts/PrintAxiomsFull.lean          # axioms of the full statement (sorryAx from GGOS/OS/Open.lean)
lake env lean scripts/PrintAxioms.lean              # axioms of the seven results it uses
lake env leanchecker GGOS.OS.Statement              # kernel replay of one module (repeat per module)
```

## License

Apache License 2.0 ([LICENSE](LICENSE)). The paper [GG-OS] is not included; cite it as above.
