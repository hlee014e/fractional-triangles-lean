# Fractional Triangles — Lean Verification

Lean 4 verification accompanying the *Fractional Triangles* manuscript.

The repository is organized according to the sections of the manuscript.
For each Lean file below, the README records the corresponding paper content and the part that is checked in Lean.

All current Lean files compile without `sorry`.

## Build

```bash
lake build
```

---

# Section 2 — Grading group and roots

Directory: [`FractionalTriangles/Section2`](FractionalTriangles/Section2)

### [`GradingGroup.lean`](FractionalTriangles/Section2/GradingGroup.lean)

Defines the grading group

$$
L(p,q,r)=\langle \vec x,\vec y,\vec z,\vec c\mid
p\vec x=q\vec y=r\vec z=\vec c\rangle
$$

and

$$
\vec\omega=\vec c-\vec x-\vec y-\vec z.
$$

### [`ScaledDegree.lean`](FractionalTriangles/Section2/ScaledDegree.lean)

Constructs the integral scaled-degree map

$$
D=N\deg,
\qquad
D(\vec x)=\frac{N}{p},\;
D(\vec y)=\frac{N}{q},\;
D(\vec z)=\frac{N}{r},\;
D(\vec c)=N.
$$

### [`Equation22_Generators.lean`](FractionalTriangles/Section2/Equation22_Generators.lean)

Checks equation (2.2) on the generators.

### [`Equation22.lean`](FractionalTriangles/Section2/Equation22.lean)

Checks equation (2.2) for every $\vec v\in L$:

$$
N\vec v=(N\deg\vec v)\vec c.
$$

### [`Equation24.lean`](FractionalTriangles/Section2/Equation24.lean)

Formalizes

$$
L/\mathbb Z\vec c
\cong
\mathbb Z/p\mathbb Z\oplus
\mathbb Z/q\mathbb Z\oplus
\mathbb Z/r\mathbb Z.
$$

### [`Lemma21_Torsion.lean`](FractionalTriangles/Section2/Lemma21_Torsion.lean)

Checks the torsion/Bézout arithmetic used in Lemma 2.1, beginning with

$$
\deg(\vec v)=0\Longrightarrow N\vec v=0.
$$

### [`Lemma21.lean`](FractionalTriangles/Section2/Lemma21.lean)

Checks

$$
\gcd(e,N)=1
\Longrightarrow
[\vec v\mapsto e\vec v]
\text{ is injective on }L(p,q,r).
$$

### [`Theorem11_RootCriterion.lean`](FractionalTriangles/Section2/Theorem11_RootCriterion.lean)

Checks the arithmetic root criterion in Theorem 1.1.

### [`Theorem11_DegreeArithmetic.lean`](FractionalTriangles/Section2/Theorem11_DegreeArithmetic.lean)

Checks the degree/root arithmetic arising from

$$
\delta\vec\tau=\vec\omega.
$$

### [`Theorem11_MaximalRoot.lean`](FractionalTriangles/Section2/Theorem11_MaximalRoot.lean)

Checks the final maximal-root arithmetic, including the consequences corresponding to (2.5) and (2.6). In particular,

$$
d_{\max}\vec\varpi=\vec\omega,
\qquad
\delta\mid d_{\max}
\Longrightarrow
\vec\tau=\frac{d_{\max}}{\delta}\vec\varpi.
$$

### [`Main.lean`](FractionalTriangles/Section2/Main.lean)

Collects the Section 2 verification files.

---

# Section 3 — The group $G_{\vec\tau}$ and invariant-ring numerics

Directory: [`FractionalTriangles/Section3`](FractionalTriangles/Section3)

### [`ProofAudit.lean`](FractionalTriangles/Section3/ProofAudit.lean)

Checks the group-theoretic and arithmetic steps used in Propositions 3.1 and 3.2. In particular,

$$
a^\delta=1,\qquad
a^N=1,\qquad
\gcd(\delta,N)=1
\Longrightarrow
a=1.
$$

### [`Prop31Next.lean`](FractionalTriangles/Section3/Prop31Next.lean)

Checks the finite-group quotient mechanism behind (3.4):

$$
|A/\langle\tau\rangle|\,|\langle\tau\rangle|=|A|,
$$

together with the character-annihilator argument used in (3.3).

### [`Prop31Relations.lean`](FractionalTriangles/Section3/Prop31Relations.lean)

Checks the character relations in Proposition 3.1.

### [`Prop31_Eq33_GradingCharacters.lean`](FractionalTriangles/Section3/Prop31_Eq33_GradingCharacters.lean)

Connects the abstract character relations with the concrete grading characters.

### [`Prop31_Eq33_Characterization.lean`](FractionalTriangles/Section3/Prop31_Eq33_Characterization.lean)

Checks the character/arithmetic criterion used to characterize $G_{\vec\tau}$.

### [`Prop31OrderInvariants.lean`](FractionalTriangles/Section3/Prop31OrderInvariants.lean)

Checks the order and invariant-degree consequences used in Proposition 3.1.

### [`Prop31_Eq34_Order.lean`](FractionalTriangles/Section3/Prop31_Eq34_Order.lean)

Checks

$$
|\operatorname{tors}L|=\frac{pqr}{N}
$$

and the integral form

$$
N|G_{\vec\tau}|=u\,pqr.
$$

### [`Prop31_Eq35_InvariantDegrees.lean`](FractionalTriangles/Section3/Prop31_Eq35_InvariantDegrees.lean)

Checks the degree arithmetic used for the $G_{\vec\tau}$-invariant part.

### [`Prop32_Eq38_39_MolienReciprocity.lean`](FractionalTriangles/Section3/Prop32_Eq38_39_MolienReciprocity.lean)

Checks the algebraic and numerical identities used after the standard Molien/invariant-ring inputs, including the numerical parts of Proposition 3.2.

Molien's theorem, invariant-ring normality, the graded invariant-ring identification, the equivariant exact sequence, and the canonical-module theorem remain external inputs.

### [`Main.lean`](FractionalTriangles/Section3/Main.lean)

Collects the Section 3 verification files.

---

# Section 4 — Stacky reconstruction and classification

Directory: [`FractionalTriangles/Section4`](FractionalTriangles/Section4)

## Lemma 4.2

### [`Lemma42_Reconstruction.lean`](FractionalTriangles/Section4/Lemma42_Reconstruction.lean)

Checks the arithmetic core of Lemma 4.2 and isolates the stack-theoretic inputs needed for the complete reconstruction argument.

### [`Lemma42_Characters.lean`](FractionalTriangles/Section4/Lemma42_Characters.lean)

At a stacky point of order $p_i$, with character $s_i$ of $\mathcal O_X(\vec\tau)$, Lean checks

$$
\delta\vec\tau=\vec\omega
\Longrightarrow
\delta s_i\equiv-1\pmod{p_i}
\Longrightarrow
\gcd(s_i,p_i)=1.
$$

Thus the stabilizer character is faithful.

### [`Lemma42_Fiber.lean`](FractionalTriangles/Section4/Lemma42_Fiber.lean)

Checks the character/fiber obstruction leading to

$$
ms_i=0
\Longleftrightarrow
p_i\mid m.
$$

### [`Lemma42_SerreVanishing.lean`](FractionalTriangles/Section4/Lemma42_SerreVanishing.lean)

Checks the arithmetic consequence of eventual occurrence of sufficiently large multiples of $p_i$, leading to

$$
\gcd(\Sigma_{P_i})=p_i.
$$

### [`Lemma42_Polarization.lean`](FractionalTriangles/Section4/Lemma42_Polarization.lean)

Packages

$$
\delta\vec\tau=\vec\omega
\Longrightarrow
\delta s_i\equiv-1\pmod{p_i}
\Longrightarrow
s_i\in(\mathbb Z/p_i\mathbb Z)^\times
\Longrightarrow
ms_i=0\iff p_i\mid m.
$$

External geometric inputs include the Geigle–Lenzing Cox/section-ring identification, residual gerbes $B\mu_{p_i}$, the representation-theoretic description of fibers, Serre vanishing on the coarse curve, Veronese reconstruction, and the final stacky-Proj normality/isomorphism argument.

## Later Section 4 files

### [`Lemma43_45_GeometricArithmetic.lean`](FractionalTriangles/Section4/Lemma43_45_GeometricArithmetic.lean)

Contains the currently formalized discrete/arithmetic parts of the early Section 4 lemmas, including the discrete-data core used in Lemma 4.3.

### [`Lemma46_Prop47_BranchedCases.lean`](FractionalTriangles/Section4/Lemma46_Prop47_BranchedCases.lean)

Checks the case arithmetic in the graph/branched analysis leading to Proposition 4.7.

### [`Lemma48_Table2_Eq413.lean`](FractionalTriangles/Section4/Lemma48_Table2_Eq413.lean)

Checks the divisibility and gcd calculations associated with Lemma 4.8, Table 2, and (4.13).

### [`Lemma49_Thm410_Mutation.lean`](FractionalTriangles/Section4/Lemma49_Thm410_Mutation.lean)

Checks the arithmetic part of Lemma 4.9 and the subsequent classification argument, including

$$
|\det E_g|=h_0=qh.
$$

---

# Section 5 — Atomic models and divisor arithmetic

Directory: [`FractionalTriangles/Section5`](FractionalTriangles/Section5)

### [`Prop51.lean`](FractionalTriangles/Section5/Prop51.lean)

Checks the arithmetic part of Proposition 5.1, including the finite-group cardinality implication used in the order computation.

### [`AtomicDivisor.lean`](FractionalTriangles/Section5/AtomicDivisor.lean)

Checks the divisor arithmetic associated with the atomic cases and the numerical part of the classification leading to Theorem 5.6.

### [`Prop57.lean`](FractionalTriangles/Section5/Prop57.lean)

Checks the sufficiency arithmetic in Proposition 5.7.

### [`Prop57Necessity.lean`](FractionalTriangles/Section5/Prop57Necessity.lean)

Checks the necessity arithmetic in Proposition 5.7.

### [`Prop57L3.lean`](FractionalTriangles/Section5/Prop57L3.lean)

Checks the remaining $L3$ gcd/divisibility calculation and the arithmetic transition from Section 5 to Section 6.

---

# Section 6 — Finite census and low-index enumeration

Directory: [`FractionalTriangles/Section6`](FractionalTriangles/Section6)

### [`Census.lean`](FractionalTriangles/Section6/Census.lean)

Provides the arithmetic infrastructure for the finite census.

### [`IndependentLowIndex.lean`](FractionalTriangles/Section6/IndependentLowIndex.lean)

Performs an independent low-index enumeration as a cross-check.

### [`LowIndexActualEnumeration.lean`](FractionalTriangles/Section6/LowIndexActualEnumeration.lean)

Checks the implemented low-index enumeration for

$$
\delta=2,3,4,5,6.
$$

The resulting class counts are

$$
6,\ 8,\ 8,\ 21,\ 0.
$$

### [`FullCensusActual.lean`](FractionalTriangles/Section6/FullCensusActual.lean)

Carries out the full implemented census in the checked range and reproduces

$$
506
$$

class keys.

### [`Remark63_Examples.lean`](FractionalTriangles/Section6/Remark63_Examples.lean)

Checks the explicit arithmetic systems appearing in Remark 6.3.

---

# Core

Directory: [`FractionalTriangles/Core`](FractionalTriangles/Core)

### [`Arithmetic.lean`](FractionalTriangles/Core/Arithmetic.lean)

Contains small arithmetic lemmas reused by the paper-specific verification files.

---

# Formalization boundary

The repository distinguishes

$$
\boxed{\text{paper-specific deductions checked in Lean}}
$$

from

$$
\boxed{\text{standard geometric or theoretical inputs used externally}}.
$$

The Lean development focuses on arithmetic, finite-group, character, divisibility, and finite-enumeration steps.

Results requiring substantial additional infrastructure for Deligne–Mumford stacks, Geigle–Lenzing curves, stacky Proj, deformation theory, invariant-ring normality, Molien theory, or canonical modules are explicitly identified as external inputs rather than silently introduced as axioms.

The current project builds successfully with

```bash
lake build
```

and the verification files contain no `sorry`.
