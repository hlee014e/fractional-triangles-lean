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

**Section 2 — the Geigle–Lenzing grading group**

Lean constructs


```math
L(p,q,r)
=
\langle
\vec x,\vec y,\vec z,\vec c
\mid
p\vec x=q\vec y=r\vec z=\vec c
\rangle .
```


In particular it verifies the defining relations


```math
p\vec x=\vec c,\qquad
q\vec y=\vec c,\qquad
r\vec z=\vec c.
```


The dualizing element is defined exactly as in the manuscript:


```math
\vec\omega
=
\vec c-\vec x-\vec y-\vec z.
```


### [`ScaledDegree.lean`](FractionalTriangles/Section2/ScaledDegree.lean)

Constructs the integral scaled-degree map


```math
D=N\deg,
\qquad
D(\vec x)=\frac{N}{p},\;
D(\vec y)=\frac{N}{q},\;
D(\vec z)=\frac{N}{r},\;
D(\vec c)=N.
```


### [`Equation22_Generators.lean`](FractionalTriangles/Section2/Equation22_Generators.lean)

**Equation (2.2) — generator checks**

Let


```math
N=\mathrm{lcm}(p,q,r).
```


Lean verifies the scaled degrees


```math
\mathrm{sdeg}(\vec c)=N,
\qquad
\mathrm{sdeg}(\vec x)=\frac Np,
\qquad
\mathrm{sdeg}(\vec y)=\frac Nq,
\qquad
\mathrm{sdeg}(\vec z)=\frac Nr.
```


For each of the four generators it checks equation (2.2):


```math
N\vec v
=
\mathrm{sdeg}(\vec v)\,\vec c.
```


Equivalently, using the paper's degree normalization,


```math
N\vec v
=
N\deg(\vec v)\,\vec c.
```


### [`Equation22.lean`](FractionalTriangles/Section2/Equation22.lean)

**Equation (2.2) — all elements of \(L(p,q,r)\)**

The generator calculation is extended to every


```math
\vec v\in L(p,q,r).
```


Lean proves


```math
N\vec v
=
N\deg(\vec v)\,\vec c.
\tag{2.2}
```


A direct consequence used later is


```math
\deg(\vec v)=0
\Longrightarrow
N\vec v=0.
```


Thus every element in the kernel of the degree map is killed by \(N\).

### [`Equation24.lean`](FractionalTriangles/Section2/Equation24.lean)

**Equation (2.4) — quotient by \(\mathbb Z\vec c\)**

Lean constructs the residue map


```math
L(p,q,r)
\longrightarrow
\mathbb Z/p\mathbb Z
\oplus
\mathbb Z/q\mathbb Z
\oplus
\mathbb Z/r\mathbb Z
```


and proves that it is surjective with kernel


```math
\mathbb Z\vec c.
```


Hence the formalized quotient description is


```math
L/\mathbb Z\vec c
\simeq
\mathbb Z/p\mathbb Z
\oplus
\mathbb Z/q\mathbb Z
\oplus
\mathbb Z/r\mathbb Z.
\tag{2.4}
```


Lean also checks the second statement in (2.4):


```math
\vec\omega
\longmapsto
(-1,-1,-1).
```


Therefore a root equation


```math
\delta\vec\tau=\vec\omega
```


reduces componentwise to


```math
\delta s_p\equiv-1\pmod p,\qquad
\delta s_q\equiv-1\pmod q,\qquad
\delta s_r\equiv-1\pmod r.
```


### [`Lemma21_Torsion.lean`](FractionalTriangles/Section2/Lemma21_Torsion.lean)

**Lemma 2.1 — torsion mechanism**

From equation (2.2), Lean first proves


```math
\deg(\vec v)=0
\Longrightarrow
N\vec v=0.
```


It then verifies the Bézout step


```math
e\vec v=0,\qquad
N\vec v=0,\qquad
\gcd(e,N)=1
\Longrightarrow
\vec v=0.
```


This is the group-theoretic mechanism behind Lemma 2.1.

### [`Lemma21.lean`](FractionalTriangles/Section2/Lemma21.lean)

**Lemma 2.1 — injectivity of multiplication**

For the concrete grading group \(L(p,q,r)\), Lean proves


```math
\gcd(e,N)=1
\Longrightarrow
[\;e\;]\colon L(p,q,r)\to L(p,q,r)
\text{ is injective}.
```


Equivalently,


```math
e\vec v=0
\Longrightarrow
\vec v=0
\qquad
\text{when }\gcd(e,N)=1.
```


This is exactly the injectivity used at the end of the proof of Theorem 1.1.

### [`Theorem11_RootCriterion.lean`](FractionalTriangles/Section2/Theorem11_RootCriterion.lean)

**Theorem 1.1 — root index criterion and existence/uniqueness mechanism**

The admissible root-index condition is


```math
\delta\mid k,
\qquad
\gcd(\delta,N)=1.
```


Equivalently, in the Lean file,


```math
\mathrm{RootIndexAdmissible}(\delta;k,N)
\iff
\delta\mid k\ \text{ and }\ \gcd(\delta,N)=1.
```


If \(d=d_{\max}\) is the maximal admissible index, Lean verifies


```math
\mathrm{RootIndexAdmissible}(\delta;k,N)
\Longrightarrow
\delta\mid d_{\max}.
```


Once a maximal root


```math
d_{\max}\vec\varpi=\vec\omega
```


is given, every divisor \(\delta\mid d_{\max}\) produces the root


```math
\vec\tau=
\frac{d_{\max}}{\delta}\vec\varpi,
\qquad
\delta\vec\tau=\vec\omega.
```


Lean also verifies the uniqueness step


```math
[\delta]\colon L\to L\ \text{injective},
\qquad
\delta\vec\tau_1=\delta\vec\tau_2=\vec\omega
\Longrightarrow
\vec\tau_1=\vec\tau_2.
```


Thus, once the concrete necessity and injectivity results from the other
Section 2 files are supplied, the final criterion is


```math
\exists!\,\vec\tau\in L:
\delta\vec\tau=\vec\omega
\iff
\delta\mid k\ \text{ and }\ \gcd(\delta,N)=1.
```


### [`Theorem11_DegreeArithmetic.lean`](FractionalTriangles/Section2/Theorem11_DegreeArithmetic.lean)

**Theorem 1.1 — existence and uniqueness from the maximal root**

Assume that the maximal root satisfies


```math
d_{\max}\vec\varpi=\vec\omega
```


and that


```math
\delta\mid d_{\max}.
```


Lean verifies the existence calculation


```math
\delta
\left(
\frac{d_{\max}}{\delta}\vec\varpi
\right)
=
\vec\omega.
```


For any other root


```math
\delta\vec\tau=\vec\omega,
```


Lean checks the identity used in the paper:


```math
\delta
\left(
\vec\tau-
\frac{d_{\max}}{\delta}\vec\varpi
\right)
=0.
```


Using Lemma 2.1 and


```math
\gcd(\delta,N)=1,
```


this gives the uniqueness formula


```math
\vec\tau=
\frac{d_{\max}}{\delta}\vec\varpi.
```


The file also isolates the elementary degree implication


```math
k=\delta t
\Longrightarrow
\delta\mid k.
```


**Input used here:** the construction of the maximal root
\(d_{\max}\vec\varpi=\vec\omega\) is taken as a hypothesis in this file;
its explicit arithmetic construction is handled separately.

### [`Theorem11_MaximalRoot.lean`](FractionalTriangles/Section2/Theorem11_MaximalRoot.lean)

**Theorem 1.1 — equations (2.5), (2.6), and the maximal root**

From the residue congruences


```math
\delta s_p\equiv -1\pmod p,\qquad
\delta s_q\equiv -1\pmod q,\qquad
\delta s_r\equiv -1\pmod r,
```


Lean proves


```math
\gcd(\delta,p)=
\gcd(\delta,q)=
\gcd(\delta,r)=1,
```


and hence, for


```math
N=\mathrm{lcm}(p,q,r),
```



```math
\gcd(\delta,N)=1.
```


This is the arithmetic content of equation (2.5).

For equation (2.6), suppose


```math
b_p p\equiv1\pmod d,\qquad
b_q q\equiv1\pmod d,\qquad
b_r r\equiv1\pmod d.
```


Lean extracts integral coefficients


```math
b_p p-1=dB_x,\qquad
b_q q-1=dB_y,\qquad
b_r r-1=dB_z,
```


and, assuming


```math
1-b_p-b_q-b_r=dA,
```


checks directly that


```math
\vec\varpi
=
A\vec c+B_x\vec x+B_y\vec y+B_z\vec z
```


satisfies


```math
d\vec\varpi=\vec\omega.
```


Thus, for \(d=d_{\max}\), this verifies the algebra in the explicit maximal-root
formula (2.6).

Finally, if


```math
\delta\mid d_{\max},
\qquad
\delta\vec\tau=\vec\omega,
\qquad
d_{\max}\vec\varpi=\vec\omega,
```


and


```math
\gcd(\delta,N)=1,
```


Lean verifies


```math
\vec\tau=
\frac{d_{\max}}{\delta}\vec\varpi.
```


### [`Main.lean`](FractionalTriangles/Section2/Main.lean)

Collects the Section 2 verification files.

---

# Section 3 — invariant ring and Hilbert-series calculations

Directory: [`FractionalTriangles/Section3`](FractionalTriangles/Section3)

The files in this section verify the algebraic, group-theoretic, and numerical
steps in Propositions 3.1 and 3.2.  The statements below emphasize the
paper-level formulas rather than elementary helper lemmas.

### [`Prop31_Eq33_GradingCharacters.lean`](FractionalTriangles/Section3/Prop31_Eq33_GradingCharacters.lean)

**Proposition 3.1 — grading relations behind equation (3.3)**

For a character of the actual grading group


```math
\chi:L(p,q,r)\longrightarrow G,
```


write


```math
\alpha_x=\chi(\vec x),\qquad
\alpha_y=\chi(\vec y),\qquad
\alpha_z=\chi(\vec z),\qquad
\rho=\chi(\vec c).
```


From


```math
p\vec x=q\vec y=r\vec z=\vec c,
```


Lean derives, rather than assumes,


```math
\alpha_x^p=\rho,\qquad
\alpha_y^q=\rho,\qquad
\alpha_z^r=\rho.
```



### [`Prop31_Eq33_Characterization.lean`](FractionalTriangles/Section3/Prop31_Eq33_Characterization.lean)

**Proposition 3.1, equation (3.3) — characterization of \(G_\tau\)**

Assume the paper's relations


```math
\delta\vec\tau=\vec\omega,
\qquad
N\vec\tau=u\vec c,
\qquad
\gcd(\delta,N)=1.
```


Lean proves the actual-character equivalence


```math
\chi(\vec\tau)=1
```


if and only if


```math
\begin{aligned}
\alpha_x^p&=\rho,\\
\alpha_y^q&=\rho,\\
\alpha_z^r&=\rho,\\
\rho&=\alpha_x\alpha_y\alpha_z,\\
\rho^u&=1.
\end{aligned}
\tag{3.3}
```


In particular, the product equation follows from


```math
\vec\omega=\vec c-\vec x-\vec y-\vec z,
```


since


```math
\chi(\vec\omega)
=
\frac{\rho}{\alpha_x\alpha_y\alpha_z}.
```


The converse uses both


```math
\chi(\vec\tau)^\delta=1,
\qquad
\chi(\vec\tau)^N=1,
```


together with


```math
\gcd(\delta,N)=1.
```



### [`Prop31Relations.lean`](FractionalTriangles/Section3/Prop31Relations.lean)

**Equation (3.3) — relation layer**

This file verifies explicitly the two nontrivial relations entering (3.3):


```math
\chi(\vec\omega)=1
\iff
\rho=\alpha_x\alpha_y\alpha_z
```


and, from


```math
N\vec\tau=u\vec c,
```



```math
\chi(\vec\tau)=1
\Longrightarrow
\rho^u=1.
```


These relations are then assembled in
`Prop31_Eq33_Characterization.lean` for actual characters of \(L(p,q,r)\).


### [`Prop31_Eq34_Order.lean`](FractionalTriangles/Section3/Prop31_Eq34_Order.lean)

**Proposition 3.1, equation (3.4) — order of the finite group**

Using


```math
|\mathrm{tors}L|
=
\frac{pqr}{N}
```


and the index contribution coming from \(\vec\tau\), Lean verifies the
cardinality calculation leading to


```math
|G_\tau|
=
\mu pqr
\tag{3.4}
```


when


```math
u=N\mu.
```


In particular, the arithmetic reduction checked in Lean is


```math
u\,\frac{pqr}{N}
=
(N\mu)\frac{pqr}{N}
=
\mu pqr.
```



### [`Prop31Next.lean`](FractionalTriangles/Section3/Prop31Next.lean)

**Finite-group quotient step used in equation (3.4)**

For a finite abelian group \(A\) and \(\tau\in A\), Lean verifies


```math
|A/\langle\tau\rangle|\,
|\langle\tau\rangle|
=
|A|.
```


This supplies the finite-group cardinality mechanism used in the derivation
of (3.4).


### [`Prop31OrderInvariants.lean`](FractionalTriangles/Section3/Prop31OrderInvariants.lean)

**Proposition 3.1 — finite extension and character separation**

Lean verifies the abstract finite-group cardinality step needed for (3.4)
and the character-separation principle used before (3.5):


```math
\chi(x)=1\text{ for every character }\chi
\Longrightarrow x=0
```


under the stated character-separation hypothesis.


### [`Prop31_Eq35_InvariantDegrees.lean`](FractionalTriangles/Section3/Prop31_Eq35_InvariantDegrees.lean)

**Proposition 3.1, equation (3.5) — invariant-degree criterion**

For the quotient degree group, Lean formalizes the character-annihilator
criterion and proves


```math
\text{degree }v\text{ is invariant under all characters}
\iff
v\in\mathbb Z\vec\tau.
\tag{3.5}
```


Thus the invariant degrees are precisely the multiples of the root
\(\vec\tau\), assuming the stated character-separation property.


### [`Prop32_Eq38_39_MolienReciprocity.lean`](FractionalTriangles/Section3/Prop32_Eq38_39_MolienReciprocity.lean)

**Equations (3.8)–(3.9) and Proposition 3.2**

This file verifies the algebraic and numerical calculations used after
applying Molien's formula.

For a group element satisfying


```math
\alpha_x^p=\alpha_y^q=\alpha_z^r=\rho,
\qquad
\rho=\alpha_x\alpha_y\alpha_z,
```


Lean checks the inversion identity used in the transformed Molien summand.

It also verifies the exponent calculation


```math
\nu
=
1-\frac1p-\frac1q-\frac1r,
\qquad
\nu=\mu\delta
```


implies


```math
\frac1\mu
-\frac1{\mu p}
-\frac1{\mu q}
-\frac1{\mu r}
=
\delta.
\tag{3.9}
```


For a hypersurface Hilbert series


```math
H(t)
=
\frac{1-t^h}
{(1-t^a)(1-t^b)(1-t^c)},
```


the reciprocity exponent comparison gives the numerical relation


```math
h-a-b-c=\delta.
```


The identity contribution to the pole at \(t=1\) is checked to have
coefficient


```math
\mu^2pqr,
```


and division by


```math
|G_\tau|=\mu pqr
```


gives


```math
\mu.
```


Hence comparison with the hypersurface pole coefficient


```math
\frac{h}{abc}
```


gives the second numerical identity of Proposition 3.2:


```math
\frac{h}{abc}=\mu.
```


The file also records the corresponding canonical-module numerical shift.


### What Section 3 does **not** claim to formalize

The Lean files verify the character calculations, finite-group arithmetic,
Molien-summand algebra, reciprocity exponents, and pole coefficients above.

They do **not** claim a Lean proof of the external commutative-algebra input
itself, in particular:


```math
\text{Molien's theorem},
```


or the full theory of invariant-ring normality/canonical modules used in the
paper.  Those are treated as mathematical inputs; the calculations made from
them are what is checked here.

---

# Section 4 — Stacky reconstruction and classification

Directory: [`FractionalTriangles/Section4`](FractionalTriangles/Section4)

## Lemma 4.2

### [`Lemma42_Reconstruction.lean`](FractionalTriangles/Section4/Lemma42_Reconstruction.lean)

**Lemma 4.2 — reconstruction: arithmetic core**

For a stacky point of order \(p_i\), define


```math
\Sigma_{P_i}
=
\left\{
m\ge1\;:\;
\exists\,s\in H^0(X,\mathcal L^m),
\quad
s(P_i)\neq0
\right\}.
```


The stabilizer of the reconstructed stack is governed by


```math
\mathrm{Stab}(P_i)
=
\mu_{\gcd(\Sigma_{P_i})}.
```


The Lean-checked arithmetic part begins with the root-character relation


```math
\delta s_i\equiv -1\pmod{p_i}.
```


If a section of degree \(m\) can have nonzero value at \(P_i\), its fiber
character must be trivial:


```math
m s_i\equiv0\pmod{p_i}.
```


Lean proves


```math
\delta s_i\equiv-1\pmod{p_i},
\qquad
m s_i\equiv0\pmod{p_i}
\Longrightarrow
p_i\mid m.
```


Thus


```math
m\in\Sigma_{P_i}
\Longrightarrow
p_i\mid m.
```


The geometric Serre-vanishing argument in the paper supplies the converse
eventually:


```math
m\gg0,\qquad p_i\mid m
\Longrightarrow
m\in\Sigma_{P_i}.
```


Lean then proves from these two properties that


```math
\gcd(\Sigma_{P_i})=p_i.
```


Consequently the group-theoretic stabilizer calculation becomes


```math
\{\lambda\in\mathbb G_m:
\lambda^m=1\text{ for every }m\in\Sigma_{P_i}\}
=
\mu_{p_i}.
```


More generally Lean proves


```math
\left(
\forall m\in\Sigma,\ \lambda^m=1
\right)
\iff
\lambda^{\gcd(\Sigma)}=1.
```


**External geometric input:** the Cox/section identification, residual-gerbe
evaluation sequence, Serre vanishing, stacky Proj reconstruction, and the final
normalization/isomorphism argument are not formalized in Lean here.

### [`Lemma42_Characters.lean`](FractionalTriangles/Section4/Lemma42_Characters.lean)

At a stacky point of order $p_i$, with character $s_i$ of $\mathcal O_X(\vec\tau)$, Lean checks


```math
\delta\vec\tau=\vec\omega
\Longrightarrow
\delta s_i\equiv-1\pmod{p_i}
\Longrightarrow
\gcd(s_i,p_i)=1.
```


Thus the stabilizer character is faithful.

### [`Lemma42_Fiber.lean`](FractionalTriangles/Section4/Lemma42_Fiber.lean)

**Lemma 4.2 — fiber characters at the stacky points**

At a stacky point of order \(p\), the root equation gives


```math
\delta s\equiv-1\pmod p.
```


Lean proves the exact criterion


```math
ms\equiv0\pmod p
\iff
p\mid m.
```


Hence


```math
p\nmid m
\Longrightarrow
ms\not\equiv0\pmod p,
```


so the character of \(\mathcal L^m\) on the residual gerbe is nontrivial.

Lean also checks the elementary invariant-vector implication


```math
a\neq1,\qquad av=v
\Longrightarrow
v=0.
```


For the three stacky points the root equation
\(\delta\vec\tau=\vec\omega\) gives simultaneously


```math
\delta s_p=-1\in\mathbb Z/p,
\quad
\delta s_q=-1\in\mathbb Z/q,
\quad
\delta s_r=-1\in\mathbb Z/r.
```


### [`Lemma42_SerreVanishing.lean`](FractionalTriangles/Section4/Lemma42_SerreVanishing.lean)

**Lemma 4.2 — arithmetic behind the Serre-vanishing step**

For \(M>0\), Lean verifies


```math
m=
\left\lfloor\frac mM\right\rfloor M+(m\bmod M),
\qquad
0\le m\bmod M<M.
```


Suppose that for every residue class \(r\bmod M\) there is a threshold
\(Q_r\) after which a property holds.

Lean proves that the finitely many thresholds can be replaced by one common
threshold:


```math
\exists Q\;
\forall r<M,\;
q\ge Q
\Longrightarrow
P(q,r).
```


Consequently,


```math
m\gg0
\Longrightarrow
P\!\left(
\left\lfloor\frac mM\right\rfloor,
m\bmod M
\right).
```


This is the finite-residue arithmetic used in the paper's phrase
“Serre vanishing, applied in the finitely many residue classes of \(m\).”

**External input:** Serre vanishing itself is not proved in Lean here.

### [`Lemma42_Polarization.lean`](FractionalTriangles/Section4/Lemma42_Polarization.lean)

**Lemma 4.2 — polarization \(\mathcal O(1)\) and faithful stabilizer characters**

For


```math
S_m=T_{m\vec\tau},
\qquad
Y=\mathrm{Proj}^{st}S,
```


the paper uses


```math
f^*\mathcal O_Y(1)\simeq\mathcal O_X(\vec\tau).
```


Taking this geometric identification as input, Lean verifies at each stacky
point


```math
\delta\,\mathrm{char}\mathcal O(1)=-1.
```


For a point of stabilizer order \(p\), Lean proves


```math
\delta s=-1\in\mathbb Z/p
\Longrightarrow
\xi s=0\Longrightarrow\xi=0.
```


Thus the \(\mathcal O(1)\)-character is faithful.

Lean then verifies the group-theoretic implication


```math
\chi\circ\phi\text{ injective}
\Longrightarrow
\phi\text{ injective},
```


which is the stabilizer-injectivity step used before the standard
representability criterion.

**External geometric input:** the identification


```math
f^*\mathcal O_Y(1)\simeq\mathcal O_X(\vec\tau)
```


and the stack-theoretic representability criterion.

### [`Lemma43_45_GeometricArithmetic.lean`](FractionalTriangles/Section4/Lemma43_45_GeometricArithmetic.lean)

**Definition 4.1 and Lemmas 4.3–4.5 — numerical and arithmetic parts**

For Definition 4.1, primitive weights are encoded as


```math
\gcd(A,B,C)=1.
```


#### Lemma 4.3

The geometric statement of Lemma 4.3 concerns local constancy of stabilizer
and orbifold data in families.

Lean records only the elementary discrete-data principle underlying that step:


```math
f(x)=f(y)\ \text{for all }x,y
\Longrightarrow
f\text{ is constant}.
```


**External geometric input for Lemma 4.3:** relative inertia, tame local
quotient structure, linear reductivity, coarse-space base change, and the
standard local orbifold-curve model.

#### Lemma 4.4

The numerical degree appearing in the proof is


```math
\deg\mathcal O_C(1)
=
\frac{h}{ABC}.
```


The rigidity statement itself is geometric and is **not** claimed to be
formalized here.

**External geometric input for Lemma 4.4:** irreducibility of the quasismooth
locus, smooth proper tame DM-curve families, local constancy of genus and
stabilizer data, the root-stack description, the Picard sequence, and
\(\mathrm{Pic}^0(\mathbb P^1)=0\).

#### Lemma 4.5 and equation (4.4)

For an open coordinate line involving weights \(A_i,A_j\), the stabilizer
order used in the paper is


```math
r=\gcd(A_i,A_j).
```


The weighted-adjunction input is


```math
\frac{\delta h}{ABC}
=
2g-2+
\sum_{i=1}^{3}
\left(1-\frac1{r_i}\right).
```


Lean verifies that this is algebraically equivalent to the displayed equation
(4.4):


```math
2g
=
\frac{\delta h}{ABC}
-1
+\frac1{r_1}
+\frac1{r_2}
+\frac1{r_3}.
\tag{4.4}
```


**External geometric input for Lemma 4.5:** the actual quotient-stack
stabilizer calculation, the effective weighted-torus coordinate, the
quasismoothness/distinct-root argument, weighted adjunction, and the geometric
degree formula.

### [`Lemma46_Prop47_BranchedCases.lean`](FractionalTriangles/Section4/Lemma46_Prop47_BranchedCases.lean)

**Lemma 4.6 and Proposition 4.7 — exclusion of the two branched ternary cases**

#### Lemma 4.6 — five atomic types

The ternary support classification has seven skeletons


```math
\mathrm{FFF},\quad
\mathrm{C2F},\quad
\mathrm{Branched3},\quad
\mathrm{L2F},\quad
\mathrm{C3},\quad
\mathrm{Branched6},\quad
\mathrm{L3}.
```


Among these, Lean records the five atomic types


```math
\mathrm{FFF},\quad
\mathrm{C2F},\quad
\mathrm{L2F},\quad
\mathrm{C3},\quad
\mathrm{L3}
```


and identifies


```math
\mathrm{Branched3},\qquad
\mathrm{Branched6}
```


as the two cases to be excluded in Proposition 4.7.

**External input for Lemma 4.6:** the fact that these seven cases exhaust the
ternary possibilities comes from the classical ternary graph/support
classification; Lean does not reprove that classification.

#### Proposition 4.7 — the \(f_3\) branched case

Lean verifies the point-count arithmetic used in (4.7).

If both open-line contributions are active, with


```math
r\ge1,\qquad s\ge1,
```


then


```math
1+1+r+s\ge4.
```


Thus this case cannot give exactly three stacky points.

The Case (II) divisibility contradiction is also checked:


```math
C\mid e,\qquad
\gcd(B,C)=1,\qquad
C>1
```


implies


```math
C\nmid(e+1)B.
```


For the genus expression occurring in equation (4.8), Lean proves


```math
2(a_0-1)(2e_0+1)+e_0>0
\tag{4.8}
```


whenever


```math
a_0\ge1,\qquad e_0\ge1.
```


This supplies the final numerical contradiction in the \(f_3\) branched case.

#### Proposition 4.7 — the \(f_6\) branched case

For the second branched case, Lean checks the point-count consequence


```math
2+d=3,\qquad d\ge1
\Longrightarrow
d=1.
```


It also verifies the positivity used after equation (4.11):


```math
d(a-1)+x>0
\tag{4.11}
```


for


```math
d\ge1,\qquad a\ge2,\qquad x>0.
```


Finally, Lean checks the positivity appearing in equation (4.12):


```math
et+e+t-1>0
\tag{4.12}
```


for


```math
e\ge1,\qquad t\ge1.
```


Hence the explicit numerical expressions used at the end of both branched
cases are strictly positive in the required ranges.

**What remains external for the full Proposition 4.7:** Lemma 4.4 deformation
rigidity, the geometric stacky-stratum count and weighted adjunction from
Lemma 4.5, the derivation of the displayed weights from weighted homogeneity,
and the support/classification theorem of Lemma 4.6.

### [`Lemma48_Table2_Eq413.lean`](FractionalTriangles/Section4/Lemma48_Table2_Eq413.lean)

**Lemma 4.8 — Table 2 and the arithmetic behind (4.13)**

This file checks the divisibility and primitivity arithmetic used in the
coordinate-stratum analysis of Lemma 4.8.

#### FFF case

For the raw weights


```math
(bc,\;ac,\;ab),
```


Lean proves that if


```math
\gcd(a,b)=\gcd(a,c)=\gcd(b,c)=1,
```


then


```math
\gcd(bc,ac,ab)=1.
```


Thus the FFF raw weight triple is primitive under the pairwise-coprimality
hypothesis.

#### C2F case

For the raw weights


```math
\bigl(c(b-1),\;ac,\;ab\bigr),
```


put


```math
r=\gcd(a,b-1),
\qquad
s=\gcd(b,c).
```


Lean verifies


```math
r\mid c(b-1),\qquad
r\mid ac,\qquad
r\mid ab,
```


and also


```math
s\mid c(b-1),\qquad
s\mid ac,\qquad
s\mid ab.
```


Hence both gcd factors occurring in the C2F reduction divide every raw
weight.

#### L2F case

For the raw weights


```math
\bigl(c(b-1),\;c(a-1),\;ab-1\bigr),
```


let


```math
d=\gcd(a-1,b-1).
```


Lean proves


```math
d\mid c(b-1),\qquad
d\mid c(a-1),\qquad
d\mid ab-1.
```


The last divisibility uses the identity


```math
ab-1
=
(a-1)(b-1)+(a-1)+(b-1).
```


#### C3 case

For the raw weights


```math
\bigl(c(b-1)+1,\;a(c-1),\;ab\bigr),
```


put


```math
d=\gcd(b,c-1).
```


Lean verifies


```math
d\mid c(b-1)+1,\qquad
d\mid a(c-1),\qquad
d\mid ab.
```


The first divisibility is the arithmetic consequence of


```math
b\equiv0\pmod d,
\qquad
c\equiv1\pmod d.
```


These are the common-divisor reductions used in the numerical analysis
leading to the signatures in equation (4.13).

**What remains external for the full Lemma 4.8 and Table 2:** the geometric
statement that Table 2 is exhaustive.  This requires restricting each atomic
polynomial to the coordinate vertices and open coordinate lines, applying
Lemma 4.5 to determine the stacky strata, and excluding additional
dense-torus stabilizer strata.

### [`Lemma49_Thm410_Mutation.lean`](FractionalTriangles/Section4/Lemma49_Thm410_Mutation.lean)

**Lemma 4.9 and Theorem 4.10 — mutation arithmetic and weighted-Euler step**

#### Lemma 4.9

Lean checks the integer case analysis used in the primitive atomic mutation
argument.

For the FFF case,


```math
q(a-1)=a,
\qquad
q>1,\quad a\ge2
```


forces


```math
q=2,\qquad a=2.
```


In the remaining FFF case, under


```math
3\mid q,\qquad
a,b\ge3,
```


the equation


```math
q(ab-a-b)=ab
```


forces


```math
q=a=b=3.
```


For the corresponding C2F cases, Lean likewise verifies


```math
q(a-1)=a
\Longrightarrow
q=a=2,
```


and


```math
q(c-1)=c
\Longrightarrow
q=c=2.
```


It also checks the remaining small-factor alternative


```math
e(c-1)=2,
\qquad
e\ge1,\quad c\ge2,
```


which gives exactly


```math
(e,c)=(1,3)
\quad\text{or}\quad
(e,c)=(2,2).
```


These are the integer possibilities used in the case analysis following
equation (4.14).

#### Theorem 4.10 — mixed quadratic case

Lean checks the contradiction used when


```math
A+B=h,
\qquad
C>0,
```


while positivity would require


```math
h-A-B-C>0.
```


Indeed,


```math
h=A+B
```


gives


```math
h-A-B-C=-C<0,
```


contradicting the required positivity.

Hence this numerical configuration is impossible.

#### Theorem 4.10 — weighted Euler identity

For a weighted-homogeneous polynomial \(F\) of weighted degree \(h\),


```math
hF
=
AxF_x+ByF_y+CzF_z.
```


Lean verifies that at a critical point


```math
F_x=F_y=F_z=0
```


one has


```math
hF=0.
```


If


```math
h\neq0,
```


then


```math
F=0.
```


Thus every critical point lies on the hypersurface.  This is the
weighted-Euler step used in the quasismoothness argument of Theorem 4.10.

**Scope:** this file checks the displayed integer case arithmetic and the
weighted-Euler implication above.  It does not claim to formalize the full
geometric mutation/classification argument of Theorem 4.10.

### [`Prop51.lean`](FractionalTriangles/Section5/Prop51.lean)

**Proposition 5.1 — determinant condition and residual diagonal symmetry**

For an invertible polynomial with exponent matrix \(A\), the paper uses


```math
|G_f|=|\det A|
```


for the diagonal symmetry group \(G_f\), and


```math
|\langle J_f\rangle|=h
```


for the exponential grading subgroup.

Lean verifies the finite-group equivalence


```math
|\det A|=h
\iff
G_f=\langle J_f\rangle.
\tag{5.1}
```


More abstractly, for a subgroup \(J\le G\),


```math
|G|=D,\qquad |J|=h
```


implies


```math
D=h
\iff
J=G.
```


Thus equality of the two orders is exactly the condition that no residual
diagonal symmetry remains after quotienting by the grading subgroup.

**External standard inputs for the full Proposition 5.1:**

The torus-kernel formula is

```math
|G_f|=|\det A|.
```

Weighted homogeneity gives

```math
J_f\in G_f.
```

The order of the exponential grading element is

```math
|J_f|
=
\mathrm{lcm}_j
\frac{h}{\gcd(h,a_j)}.
```

For primitive weights this simplifies to

```math
|J_f|=h.
```

The Lean file checks the final finite-group cardinality implication once these
standard inputs are supplied.

### [`AtomicDivisor.lean`](FractionalTriangles/Section5/AtomicDivisor.lean)

**Table 3, Lemma 5.4, Proposition 5.5, and Theorem 5.6 — arithmetic and divisor parametrization**

#### Table 3 — the five atomic equations

Lean checks the following equivalent forms of the Table 3 equations.

For FFF,


```math
\delta
=
\alpha\beta\gamma
-\alpha\beta-\alpha\gamma-\beta\gamma.
```


For C2F,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta+\delta
```


is rewritten as


```math
(\gamma-1)(\alpha-1)(\beta-1)
=
(\alpha-1)+(\beta-1)+\delta+1.
```


For L2F,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta-1+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1)
=
(\alpha-1)+(\beta-1)+\delta.
```


For C3,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta-\alpha+1+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1)
=
(\beta-1)+\delta+1.
```


For L3,


```math
\gamma(\alpha-1)(\beta-1)
=
\alpha\beta-\alpha-\beta+2+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1)=\delta+1.
```


#### Lemma 5.4 — elementary finiteness bounds

Lean verifies the inequalities used to bound the atomic parameters.

If


```math
(A-1)(B-1)\le \delta+2,
\qquad
A,B\ge1,
```


then


```math
A\le\delta+3,
\qquad
B\le\delta+3.
```


If


```math
(A-1)B\le\delta+1,
\qquad
B\ge1,
```


then


```math
A\le\delta+2.
```


In the FFF case with \(\alpha=2\),


```math
(\beta-2)(\gamma-2)=\delta+4,
\qquad
\beta,\gamma\ge2,
```


implies


```math
\beta\le\delta+6,
\qquad
\gamma\le\delta+6.
```


These are the elementary numerical bounds used in the finiteness argument.

#### Proposition 5.5 — equation (5.2)

Lean checks the positivity implication coming from


```math
\frac{\delta h}{abc}
=
1-\frac1p-\frac1q-\frac1r.
\tag{5.2}
```


Thus


```math
1-\frac1p-\frac1q-\frac1r>0
```


implies


```math
\frac{\delta h}{abc}>0.
```


**External for the full Proposition 5.5:** the Table 4 Cox monomial identities
and the injectivity/Hilbert-function argument are not formalized in this file.

#### Theorem 5.6 — completed-product divisor identities

For the C2F equation


```math
tAB=A+B+\delta+1,
```


Lean proves


```math
(tA-1)(tB-1)
=
t(\delta+1)+1.
```


For L2F,


```math
tAB=A+B+\delta
```


gives


```math
(tA-1)(tB-1)
=
t\delta+1.
```


For FFF, writing


```math
\alpha=A+1,
```


the Table 3 equation


```math
(A+1)\beta\gamma
-(A+1)\beta
-(A+1)\gamma
-\beta\gamma
=
\delta
```


is transformed into


```math
\bigl(A(\beta-1)-1\bigr)
\bigl(A(\gamma-1)-1\bigr)
=
A\delta+(A+1)^2.
```


This is the completed-product identity used for the FFF divisor
parametrization.

Lean also verifies the recovery-integrality step


```math
U\equiv -1\pmod t
```


in the natural-number form


```math
U\bmod t=(t-1)\bmod t,
\qquad t>0,
```


which implies


```math
t\mid U+1.
```


Thus the arithmetic transformations that turn the atomic equations into
finite divisor problems are Lean-checked.

**External for the full Lemma 5.4 / Proposition 5.5 / Theorem 5.6:** the atomic
classification, the exact Table 4 Cox lifts and polynomial identities,
normality and weighted-adjunction geometry, the finite torus-map and
Hilbert-function arguments, and the converse reconstruction from atomic data.
### [`Prop57.lean`](FractionalTriangles/Section5/Prop57.lean), [`Prop57Necessity.lean`](FractionalTriangles/Section5/Prop57Necessity.lean), [`Prop57L3.lean`](FractionalTriangles/Section5/Prop57L3.lean)

**Proposition 5.7 — closed primitivity criteria**

These three files formalize the number-theoretic primitivity criteria for all
five atomic families.

#### FFF

For the raw weights


```math
(\beta\gamma,\alpha\gamma,\alpha\beta),
```


Lean proves the exact equivalence


```math
\gcd(\beta\gamma,\alpha\gamma,\alpha\beta)=1
\iff
\gcd(\alpha,\beta)=
\gcd(\beta,\gamma)=
\gcd(\gamma,\alpha)=1.
```


Thus primitivity is equivalent to pairwise coprimality of


```math
\alpha,\beta,\gamma.
```


#### C2F

For the weights


```math
\bigl(
B(t+1),\,
(A+1)(t+1),\,
(A+1)(B+1)
\bigr),
```


Lean proves that primitivity is equivalent to the three closed conditions


```math
\gcd(A+1,B)=1,
```



```math
\gcd(A+1,t+1)=1,
```


and


```math
\gcd(t+1,B+1)=1.
```


The sufficiency direction is proved in `Prop57.lean`, and all three necessity
directions are proved in `Prop57Necessity.lean`.

#### L2F

For the weights


```math
\bigl(
B(t+1),\,
A(t+1),\,
AB+A+B
\bigr),
```


Lean proves that primitivity is equivalent to


```math
\gcd(A,B)=1
```


and


```math
\gcd(t+1,AB+A+B)=1.
```


Again, sufficiency and necessity are both Lean-checked.

#### C3

For the weights


```math
\bigl(
B(t+1)+1,\,
t(A+1),\,
(A+1)(B+1)
\bigr),
```


Lean proves that primitivity is equivalent to


```math
\gcd(A+1,B(t+1)+1)=1
```


and


```math
\gcd(t,B+1)=1.
```


Both directions are formalized.

#### L3

Put


```math
m=tAB,
```


and


```math
w_1=B(t+1)+1,\qquad
w_2=t(A+1)+1,\qquad
w_3=A(B+1)+1.
```


Lean first verifies the three identities used in the paper:


```math
Aw_1=(m-1)+w_3,
```



```math
Bw_2=(m-1)+w_1,
```


and


```math
tw_3=(m-1)+w_2.
```


It also proves


```math
\gcd(m,m-1)=1.
```


From these identities Lean proves both divisibility directions in the final
gcd reduction and obtains


```math
\gcd(w_1,w_2,w_3)
=
\gcd(m-1,w_1).
```


Consequently the L3 primitivity condition reduces exactly to


```math
\gcd\bigl(tAB-1,\;B(t+1)+1\bigr)=1.
```


Thus the number-theoretic content of Proposition 5.7 is completely
Lean-checked for all five atomic families.

# Section 6 — Finite census and low-index enumeration

Directory: [`FractionalTriangles/Section6`](FractionalTriangles/Section6)

### [`Corollary61.lean`](FractionalTriangles/Section6/Corollary61.lean)

**Corollary 6.1 — explicit primitive families for \(6\nmid\delta\)**

If


```math
3\nmid\delta,
```


Lean verifies that


```math
(\delta+3,\;2\delta+3,\;3)
```


is primitive:


```math
\gcd\bigl(\delta+3,\gcd(2\delta+3,3)\bigr)=1.
```


If


```math
\delta\equiv3\pmod6,
```


Lean first proves


```math
\gcd(\delta+2,\delta+4)=1
```


and then verifies that


```math
(\delta+4,\;\delta+2,\;4)
```


is primitive:


```math
\gcd\bigl(\delta+4,\gcd(\delta+2,4)\bigr)=1.
```


These are the two explicit primitive families used in Corollary 6.1 for


```math
6\nmid\delta.
```



### [`Theorem62_Enumeration.lean`](FractionalTriangles/Section6/Theorem62_Enumeration.lean), [`Theorem62_ActualEnumeration.lean`](FractionalTriangles/Section6/Theorem62_ActualEnumeration.lean), [`Theorem62_FullCensus.lean`](FractionalTriangles/Section6/Theorem62_FullCensus.lean)

**Theorem 6.2 — independent finite enumeration**

These files independently reproduce the census from the structural formulas,
rather than importing the printed census table.

A candidate is retained only when


```math
h=a+b+c+\delta
```


and


```math
\gcd(a,b,c)=1.
```


The three weights are then sorted and candidates are deduplicated by


```math
(\mathrm{sort}(a,b,c),h).
```


Thus permutations of the same weighted system are counted only once.

#### Enumeration directly from Table 3

For each fixed \(\delta\), Lean enumerates


```math
2\le \alpha,\beta,\gamma\le \delta+6,
```


using the finite bound from Lemma 5.4, and evaluates all five atomic systems.

The raw weight/degree formulas used by the executable enumeration are:


```math
\mathrm{FFF}:
\qquad
(a,b,c;h)
=
(\beta\gamma,\alpha\gamma,\alpha\beta;\alpha\beta\gamma),
```



```math
\mathrm{C2F}:
\qquad
(a,b,c;h)
=
(\gamma(\beta-1),\alpha\gamma,\alpha\beta;\alpha\beta\gamma),
```



```math
\mathrm{L2F}:
\qquad
(a,b,c;h)
=
(\gamma(\beta-1),\gamma(\alpha-1),\alpha\beta-1;
\gamma(\alpha\beta-1)),
```



```math
\mathrm{C3}:
\qquad
(a,b,c;h)
=
(\beta\gamma-\gamma+1,\alpha(\gamma-1),\alpha\beta;
\alpha\beta\gamma),
```


and


```math
\mathrm{L3}:
\qquad
(a,b,c;h)
=
(\beta\gamma-\gamma+1,\alpha\gamma-\alpha+1,
\alpha\beta-\beta+1;\alpha\beta\gamma+1).
```


Lean first independently reproduces


```math
(N_2,N_3,N_4,N_5,N_6)
=
(6,8,8,21,0).
```


For δ = 2, the six canonical systems obtained by the enumeration are


```math
\begin{aligned}
&(3,5,5;15),\\
&(3,5,7;17),\\
&(3,5,10;20),\\
&(3,7,9;21),\\
&(3,7,12;24),\\
&(3,10,15;30).
\end{aligned}
```


#### Full census for 2 ≤ δ ≤ 30

Lean independently computes


| δ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Nδ | 6 | 8 | 8 | 21 | 0 | 29 | 11 | 12 | 6 | 37 | 0 | 36 | 10 | 9 | 11 |

and

| δ | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Nδ | 40 | 2 | 46 | 11 | 12 | 9 | 55 | 3 | 28 | 16 | 18 | 10 | 52 | 0 |


These values are obtained by executable enumeration from the five Table 3
families; the printed census table is not used as input.

Finally Lean verifies


```math
\sum_{\delta=2}^{30} N_\delta=506.
```


Thus the numerical census in Theorem 6.2, including the total \(506\), is
independently reproduced in Lean from the finite structural enumeration.

**External mathematical input:** Table 3 and Lemma 5.4 must already be known
to give an exhaustive finite search space.  The census computation itself is
then executable and fully checked by Lean.


### [`Remark63_Examples.lean`](FractionalTriangles/Section6/Remark63_Examples.lean)

**Remark 6.3 — six explicit weighted hypersurface systems**

Lean checks the monomial degrees, the value


```math
\delta=h-a-b-c,
```


and primitivity for each of the six systems listed in Remark 6.3.

For \(\delta=3\),


```math
(a,b,c;h)=(4,10,13;30)
```


with


```math
xz^2+y^3+x^5y.
```


For \(\delta=4\),


```math
(a,b,c;h)=(5,6,9;24)
```


with


```math
zx^3+yz^2+y^4.
```


For \(\delta=5\), Lean checks the four systems


```math
(6,8,19;38),
\qquad
z^2+xy^4+x^5y,
```



```math
(4,7,16;32),
\qquad
z^2+xy^4+zx^4,
```



```math
(4,7,12;28),
\qquad
xz^2+y^4+x^4z,
```


and


```math
(4,7,9;25),
\qquad
yz^2+x^4z+xy^3.
```


For every example Lean verifies that all displayed monomials have degree \(h\),


```math
h-a-b-c=\delta,
```


and


```math
\gcd(a,b,c)=1.
```


Finally, Lean checks that all six systems actually occur among the
independently enumerated canonical keys from Theorem 6.2.

# Core

Directory: [`FractionalTriangles/Core`](FractionalTriangles/Core)

### [`Arithmetic.lean`](FractionalTriangles/Core/Arithmetic.lean)

Contains small arithmetic lemmas reused by the paper-specific verification files.

---

# Formalization boundary

The repository distinguishes


```math
\text{paper-specific deductions checked in Lean}
```


from


```math
\text{standard geometric or theoretical inputs used externally}.
```


The Lean development focuses on arithmetic, finite-group, character, divisibility, and finite-enumeration steps.

Results requiring substantial additional infrastructure for Deligne–Mumford stacks, Geigle–Lenzing curves, stacky Proj, deformation theory, invariant-ring normality, Molien theory, or canonical modules are explicitly identified as external inputs rather than silently introduced as axioms.

The current project builds successfully with

```bash
lake build
```

and the verification files contain no `sorry`.
