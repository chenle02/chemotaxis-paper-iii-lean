# What is proved

The primary scientific objects are positive parameters, classical stationary population/signal profiles on a finite interval, the genuine weak-H2 Neumann population phase, its Fourier coordinates, and explicit scalar/branch interfaces. Exact Lean types on the verification page control all quantifiers and hypotheses.

| Result family | Verified content | Remaining inputs / exclusions |
|---|---|---|
| Coefficients and modes | Taylor/modal identities, polynomial signs, root intervals and finite differences | Their identification with a reduced physical equation where required |
| Stationary estimates and limits | Classical mass/regularity estimates, integral-test weak limits, spike subsequences and bounded-sensitivity compactness | Stated solution regularity, parameter and subsequence assumptions; no full global branch construction |
| Actual phase coordinates | Genuine weak-H2 cosine mode, coordinate normalization, closed Fourier kernel and continuous splitting | No physical operator range or stable-spectrum identification |
| Signal and conserved-mass jets | Critical modal cubic response from actual elliptic signals; quadratic constant from eventual zero mass | Population family and phase-norm Peano expansion supplied; no center graph or invariance constructed |
| Local/global branch consumers | Consequences of explicit curves, charts, amplitudes, compactness and noncompactness interfaces | Curve existence/exhaustion, critical-parameter identity and global alternatives remain explicit |

## Scope and reference sign-off

[The complete scope ledger](scope-ledger.md) gives all 73 primary scopes with current manuscript numbering and pages. References were inherited from the frozen manuscript AUX and accepted correspondence mapping, not guessed from theorem names. The manuscript source hash is fixed in the public ledger. A numbered parent may occur in multiple overlapping rows with different proven cores.

<details>
<summary>Sign-off boundary</summary>

| Check | Meaning |
|---|---|
| Source fidelity | All mathematical Lean tokens preserved from the accepted source; one documentation comment cleaned |
| Manuscript comparison | Accepted per-scope judgments and exact conditions retained in the public summary; private review histories are not republished |
| Build and axioms | Fresh public-root source gate and complete owned axiom audit; results recorded in release receipts |
| Comparator | 108 full-tier plus 12 headline slots, distinct from all indexed declarations |
| Human review | Public export receives independent release/privacy/fidelity review; no whole-paper human or Lean approval inferred |
| Signed off by | Automated evidence and AI-assisted release review, October 2026; this is not author approval of the full paper |

</details>

## Reading exact statements

Use [the generated verification page](verification.md) for the exact Lean statements, source links, coverage classes and supplied assumptions, and the [JSON ledger](../data/public-scope-ledger.json) for the preserved scope text. Each theorem's Lean source is authoritative for its formal hypotheses. The whole paper is not Lean-certified.

## Selected statement cards

The types below are complete elaborated output from the fresh public-root source gate. Hidden binder context is not omitted. Source links are pinned to the gated source; reference numbers/pages come from the frozen manuscript AUX mapping. These supporting ingredients do not promote their numbered parents.

### Actual positive-mode normalization

**Statement.** The actual Neumann cosine mode belongs to the genuine weak-H2 phase. For positive interval length and positive mode index, its physical Fourier coordinate is one.

**Reference.** Theorem 1.3(1), p.10: supporting complement ingredient, not the global theorem.

**Compared with the reference.** Only the explicitly described ingredient is formalized; the full hypotheses are shown below and the parent boundary remains in the scope ledger.

[Lean source](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/c749b53b02211901063228f52af123419b0dbaf5/ChemotaxisBifurcation/WeakH2CosineMode.lean#L77).

<details>
<summary>Complete Lean type (elaborated output)</summary>

```text
ChemotaxisBifurcation.WeakH2CosineMode.coefficient_mode : ∀ {L : ℝ} (hL : LT.lt.{0} 0 L) (n : ℕ),
  LT.lt.{0} 0 n →
    Eq.{1} (ChemotaxisBifurcation.FourierAmplitude.coefficient hL n (ChemotaxisBifurcation.WeakH2CosineMode.mode hL n))
      1
```

</details>

<details>
<summary>Sign-off and exclusions</summary>

| Item | Scope |
|---|---|
| Status | Verified supporting ingredient with the displayed explicit hypotheses |
| Build / axioms | Fresh source build; no sorryAx; standard propext, Quot.sound, Classical.choice only |
| Statement comparison | Preserved accepted manuscript mapping; independently reviewed public-export correspondence |
| Definitions judged | Actual profile/phase/coefficient objects appear in the exact type; no implicit PDE existence inferred |
| Evidence commit | `c749b53b02211901063228f52af123419b0dbaf5` |
| Human review | No whole-paper human or Lean approval inferred |
| Not covered | Parent PDE/bifurcation/dynamical foundations stated in the ledger |
| Signed off by | Lean kernel/audit evidence and AI-assisted export review, 2026-10-22 |

</details>

### Closed literal Fourier complement

**Statement.** For positive length and mode index, the span of the actual cosine mode is complementary to the kernel of its continuous Fourier coefficient. The exported splitting is a continuous linear equivalence. This is not identification with a physical operator range or stable spectrum.

**Reference.** Theorem 1.3(1), p.10: geometric complement ingredient.

**Compared with the reference.** Only the explicitly described ingredient is formalized; the full hypotheses are shown below and the parent boundary remains in the scope ledger.

[Lean source](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/c749b53b02211901063228f52af123419b0dbaf5/ChemotaxisBifurcation/FourierComplement.lean#L73).

<details>
<summary>Complete Lean type (elaborated output)</summary>

```text
ChemotaxisBifurcation.FourierComplement.isCompl_span_complement : ∀ {L : ℝ} (hL : LT.lt.{0} 0 L) (n : ℕ),
  LT.lt.{0} 0 n →
    IsCompl.{0}
      (Submodule.span.{0, 0} ℝ (Singleton.singleton.{0, 0} (ChemotaxisBifurcation.WeakH2CosineMode.mode hL n)))
      (ChemotaxisBifurcation.FourierComplement.complement hL n)
```

</details>

<details>
<summary>Sign-off and exclusions</summary>

| Item | Scope |
|---|---|
| Status | Verified supporting ingredient with the displayed explicit hypotheses |
| Build / axioms | Fresh source build; no sorryAx; standard propext, Quot.sound, Classical.choice only |
| Statement comparison | Preserved accepted manuscript mapping; independently reviewed public-export correspondence |
| Definitions judged | Actual profile/phase/coefficient objects appear in the exact type; no implicit PDE existence inferred |
| Evidence commit | `c749b53b02211901063228f52af123419b0dbaf5` |
| Human review | No whole-paper human or Lean approval inferred |
| Not covered | Parent PDE/bifurcation/dynamical foundations stated in the ledger |
| Signed off by | Lean kernel/audit evidence and AI-assisted export review, 2026-10-22 |

</details>

### Fixed-mean affine uniqueness

**Statement.** Each supplied fixed-mean population decomposes uniquely around the specified homogeneous population into cosine amplitude and mean-zero Fourier-orthogonal remainder. This statement does not separately export a continuous equivalence on the mean-zero subtype.

**Reference.** Theorem 1.3(2)-(3), ambient-limit proof paragraphs, p.10: supporting phase decomposition, not the whole closure theorem.

**Compared with the reference.** Only the explicitly described ingredient is formalized; the full hypotheses are shown below and the parent boundary remains in the scope ledger.

[Lean source](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/c749b53b02211901063228f52af123419b0dbaf5/ChemotaxisBifurcation/FourierComplement.lean#L111).

<details>
<summary>Complete Lean type (elaborated output)</summary>

```text
ChemotaxisBifurcation.FourierComplement.existsUnique_fixedMean_decomposition : ∀ {L : ℝ} (hL : LT.lt.{0} 0 L) (n : ℕ),
  LT.lt.{0} 0 n →
    ∀ (U : ℝ) (J : ↥(ChemotaxisBifurcation.WeakH2PhaseSpace.Space L hL)),
      Membership.mem.{0, 0} (ChemotaxisBifurcation.WeakH2AmbientClosure.fixedMeanSet hL U) J →
        ExistsUnique.{1} fun z =>
          Membership.mem.{0, 0} (ChemotaxisBifurcation.WeakH2AmbientClosure.fixedMeanSet hL 0) z.2 ∧
            Membership.mem.{0, 0} (ChemotaxisBifurcation.FourierComplement.complement hL n) z.2 ∧
              Eq.{1} J
                (HAdd.hAdd.{0, 0, 0}
                  (HAdd.hAdd.{0, 0, 0} (ChemotaxisBifurcation.WeakH2PhaseSpace.const hL U)
                    (HSMul.hSMul.{0, 0, 0} z.1 (ChemotaxisBifurcation.WeakH2CosineMode.mode hL n)))
                  z.2)
```

</details>

<details>
<summary>Sign-off and exclusions</summary>

| Item | Scope |
|---|---|
| Status | Verified supporting ingredient with the displayed explicit hypotheses |
| Build / axioms | Fresh source build; no sorryAx; standard propext, Quot.sound, Classical.choice only |
| Statement comparison | Preserved accepted manuscript mapping; independently reviewed public-export correspondence |
| Definitions judged | Actual profile/phase/coefficient objects appear in the exact type; no implicit PDE existence inferred |
| Evidence commit | `c749b53b02211901063228f52af123419b0dbaf5` |
| Human review | No whole-paper human or Lean approval inferred |
| Not covered | Parent PDE/bifurcation/dynamical foundations stated in the ledger |
| Signed off by | Lean kernel/audit evidence and AI-assisted export review, 2026-10-22 |

</details>

### Critical modal elliptic response

**Statement.** Given positive physical parameters, a genuine population phase-norm cubic Peano expansion with the stated critical-mode condition, an actual population representative and eventual classical Neumann elliptic signal solutions, the critical signal coefficient has the stated cubic Peano jet. Neither projected balance nor a signal jet is supplied. The population family/jet, fixed parameters, regularity and all listed conditions remain inputs. No center graph, full signal phase jet or graph invariance is proved.

**Reference.** Equation 2.42, p.20: critical signal-response ingredient, not all center-graph coefficients.

**Compared with the reference.** Only the explicitly described ingredient is formalized; the full hypotheses are shown below and the parent boundary remains in the scope ledger.

[Lean source](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/c749b53b02211901063228f52af123419b0dbaf5/ChemotaxisBifurcation/CurvedSignalResponse.lean#L294).

<details>
<summary>Complete Lean type (elaborated output)</summary>

```text
ChemotaxisBifurcation.CurvedSignalResponse.actual_phase_cubic_response : ∀ (p : ChemotaxisBifurcation.PhysicalParams)
  {L : ℝ} (hL : LT.lt.{0} 0 L),
  LT.lt.{0} 0 p.uStar →
    LT.lt.{0} 0 p.mu →
      p.SignalEquilibrium →
        ∀ (n : ℕ),
          LT.lt.{0} 0 n →
            ∀ (jet : ChemotaxisBifurcation.QuadraticJetData)
              (H3 : ↥(ChemotaxisBifurcation.WeakH2PhaseSpace.Space L hL)),
              Eq.{1} (ChemotaxisBifurcation.FourierAmplitude.coefficient hL n H3) 0 →
                ∀ (J : ℝ → ↥(ChemotaxisBifurcation.WeakH2PhaseSpace.Space L hL)) (U V dV : ℝ → ℝ → ℝ),
                  (∀ (t : ℝ) (x : ↑(Set.Icc.{0} 0 L)),
                      Eq.{1} (U t ↑x) (((ChemotaxisBifurcation.WeakH2PhaseSpace.profileCLM hL) (J t)) x)) →
                    (Asymptotics.IsLittleO.{0, 0, 0} (nhds.{0} 0)
                        (fun t =>
                          HSub.hSub.{0, 0, 0} (J t)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HSMul.hSMul.{0, 0, 0} t (ChemotaxisBifurcation.WeakH2CosineMode.mode hL n))
                                (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2)
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HSMul.hSMul.{0, 0, 0} jet.a0 (ChemotaxisBifurcation.WeakH2PhaseSpace.const hL 1))
                                    (HSMul.hSMul.{0, 0, 0} jet.a2
                                      (ChemotaxisBifurcation.WeakH2CosineMode.mode hL (HMul.hMul.{0, 0, 0} 2 n))))))
                              (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 3) H3)))
                        fun t => HPow.hPow.{0, 0, 0} t 3) →
                      (∀ᶠ (t : ℝ) in nhds.{0} 0,
                          ContinuousOn.{0, 0} (U t) (Set.Icc.{0} 0 L) ∧
                            ChemotaxisBifurcation.CosineCoefficients.NeumannW21 L (V t) (dV t) ∧
                              ∀ (x : ℝ),
                                Membership.mem.{0, 0} (Set.Ioo.{0} 0 L) x →
                                  Eq.{1}
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0} (deriv.{0, 0} (dV t) x)
                                        (HMul.hMul.{0, 0, 0} p.mu (HAdd.hAdd.{0, 0, 0} p.vStar (V t x))))
                                      (HMul.hMul.{0, 0, 0} p.nu
                                        (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} p.uStar (U t x)) p.gamma)))
                                    0) →
                        Asymptotics.IsLittleO.{0, 0, 0} (nhds.{0} 0)
                          (fun t =>
                            HSub.hSub.{0, 0, 0} (ChemotaxisBifurcation.CosineCoefficients.cosineCoeff L (V t) n)
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} t
                                  (ChemotaxisBifurcation.signalMode1 p
                                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑n) Real.pi) L) 2)))
                                (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 3)
                                  (ChemotaxisBifurcation.cubicH p
                                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑n) Real.pi) L) 2)
                                    jet))))
                          fun t => HPow.hPow.{0, 0, 0} t 3
```

</details>

<details>
<summary>Sign-off and exclusions</summary>

| Item | Scope |
|---|---|
| Status | Verified supporting ingredient with the displayed explicit hypotheses |
| Build / axioms | Fresh source build; no sorryAx; standard propext, Quot.sound, Classical.choice only |
| Statement comparison | Preserved accepted manuscript mapping; independently reviewed public-export correspondence |
| Definitions judged | Actual profile/phase/coefficient objects appear in the exact type; no implicit PDE existence inferred |
| Evidence commit | `c749b53b02211901063228f52af123419b0dbaf5` |
| Human review | No whole-paper human or Lean approval inferred |
| Not covered | Parent PDE/bifurcation/dynamical foundations stated in the ledger |
| Signed off by | Lean kernel/audit evidence and AI-assisted export review, 2026-10-22 |

</details>

### Quadratic constant from conserved mass

**Statement.** Given positive length and mode index, an actual weak-H2 population perturbation family with the specified cubic phase-norm Peano expansion and eventual zero mass, its quadratic constant coefficient vanishes. No cubic-correction mass/kernel premise is required. The family and expansion are supplied; logistic invariance coefficients and center-manifold existence are not proved.

**Reference.** Equation 2.33, p.19: separate minimal conservation ingredient; the logistic formula still needs its invariance identity.

**Compared with the reference.** Only the explicitly described ingredient is formalized; the full hypotheses are shown below and the parent boundary remains in the scope ledger.

[Lean source](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/c749b53b02211901063228f52af123419b0dbaf5/ChemotaxisBifurcation/WeakH2MeanJet.lean#L11).

<details>
<summary>Complete Lean type (elaborated output)</summary>

```text
ChemotaxisBifurcation.WeakH2MeanJet.quadratic_constant_zero : ∀ {L : ℝ} (hL : LT.lt.{0} 0 L) (n : ℕ),
  LT.lt.{0} 0 n →
    ∀ (jet : ChemotaxisBifurcation.QuadraticJetData) (H3 : ↥(ChemotaxisBifurcation.WeakH2PhaseSpace.Space L hL))
      (J : ℝ → ↥(ChemotaxisBifurcation.WeakH2PhaseSpace.Space L hL)),
      (∀ᶠ (t : ℝ) in nhds.{0} 0, Eq.{1} (ChemotaxisBifurcation.WeakH2AmbientClosure.populationMass hL (J t)) 0) →
        (Asymptotics.IsLittleO.{0, 0, 0} (nhds.{0} 0)
            (fun t =>
              HSub.hSub.{0, 0, 0} (J t)
                (HAdd.hAdd.{0, 0, 0}
                  (HAdd.hAdd.{0, 0, 0} (HSMul.hSMul.{0, 0, 0} t (ChemotaxisBifurcation.WeakH2CosineMode.mode hL n))
                    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2)
                      (HAdd.hAdd.{0, 0, 0}
                        (HSMul.hSMul.{0, 0, 0} jet.a0 (ChemotaxisBifurcation.WeakH2PhaseSpace.const hL 1))
                        (HSMul.hSMul.{0, 0, 0} jet.a2
                          (ChemotaxisBifurcation.WeakH2CosineMode.mode hL (HMul.hMul.{0, 0, 0} 2 n))))))
                  (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 3) H3)))
            fun t => HPow.hPow.{0, 0, 0} t 3) →
          Eq.{1} jet.a0 0
```

</details>

<details>
<summary>Sign-off and exclusions</summary>

| Item | Scope |
|---|---|
| Status | Verified supporting ingredient with the displayed explicit hypotheses |
| Build / axioms | Fresh source build; no sorryAx; standard propext, Quot.sound, Classical.choice only |
| Statement comparison | Preserved accepted manuscript mapping; independently reviewed public-export correspondence |
| Definitions judged | Actual profile/phase/coefficient objects appear in the exact type; no implicit PDE existence inferred |
| Evidence commit | `c749b53b02211901063228f52af123419b0dbaf5` |
| Human review | No whole-paper human or Lean approval inferred |
| Not covered | Parent PDE/bifurcation/dynamical foundations stated in the ledger |
| Signed off by | Lean kernel/audit evidence and AI-assisted export review, 2026-10-22 |

</details>
