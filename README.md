# Fractional Triangles — Lean Verification

Lean 4 verification accompanying the *Fractional Triangles* manuscript.

The repository is organized according to the sections of the manuscript.
For each Lean file below, the README records the corresponding paper content and the part that is checked in Lean.

All current Lean files compile without `sorry`.

### Proposition 5.1 — diagonal symmetry group

Lean file: `FractionalTriangles/Section5/Prop51.lean`

Status: **arithmetic/group-theoretic core verified; full geometric statement not yet completely formalized.**

Lean currently verifies:

- `determinant_condition_iff_no_residual_symmetry`

  For a finite group `G` and subgroup `J`, assuming `Nat.card G = D`
  and `Nat.card J = h`, Lean proves

      D = h ↔ J = ⊤.

  In Proposition 5.1 this gives the final implication

      |G_f| = h ↔ <J_f> = G_f,

  once the orders of `G_f` and `<J_f>` are supplied.

- `prop51_lcm_coordinate_orders`

  Assuming

      gcd(h, gcd(a, gcd(b,c))) = 1,

  Lean proves

      lcm(h/gcd(h,a),
          lcm(h/gcd(h,b), h/gcd(h,c))) = h.

  This is exactly the arithmetic identity used in the computation of
  the order of the grading element.

What Lean has **not** yet formalized in this file:

- `|G_f| = |det A|`, which uses the standard torus-kernel /
  character-lattice determinant theorem;
- the actual complex element
  `J_f = (exp(2πia/h), exp(2πib/h), exp(2πic/h))`;
- `J_f ∈ G_f` from weighted homogeneity;
- the root-of-unity identification
  `ord(exp(2πia/h)) = h/gcd(h,a)`;
- consequently, the complete theorem `ord(J_f) = h` inside the actual
  complex diagonal symmetry group.

Therefore Proposition 5.1 should currently be recorded as **partially
Lean-verified**, not as completely formalized.

Verification file contains no `sorry` and introduces no axioms.

### [`AtomicDivisor.lean`](FractionalTriangles/Section5/AtomicDivisor.lean)

**Table 3, Lemma 5.4, Proposition 5.5, and Theorem 5.6 — arithmetic and divisor parametrization**

#### Table 3 — the five atomic equations

Lean checks the following equivalent forms of the Table 3 equations.

For FFF,


```math
\delta = \alpha\beta\gamma -\alpha\beta-\alpha\gamma-\beta\gamma.
```


For C2F,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta+\delta
```


is rewritten as


```math
(\gamma-1)(\alpha-1)(\beta-1) = (\alpha-1)+(\beta-1)+\delta+1.
```


For L2F,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta-1+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1) = (\alpha-1)+(\beta-1)+\delta.
```


For C3,


```math
\gamma(\alpha-1)(\beta-1)=\alpha\beta-\alpha+1+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1) = (\beta-1)+\delta+1.
```


For L3,


```math
\gamma(\alpha-1)(\beta-1) = \alpha\beta-\alpha-\beta+2+\delta
```


gives


```math
(\gamma-1)(\alpha-1)(\beta-1)=\delta+1.
```


#### Lemma 5.4 — elementary finiteness bounds

Lean verifies the inequalities used to bound the atomic parameters.

If


```math
(A-1)(B-1)\le \delta+2, \qquad A,B\ge1,
```


then


```math
A\le\delta+3, \qquad B\le\delta+3.
```


If


```math
(A-1)B\le\delta+1, \qquad B\ge1,
```


then


```math
A\le\delta+2.
```


In the FFF case with \(\alpha=2\),


```math
(\beta-2)(\gamma-2)=\delta+4, \qquad \beta,\gamma\ge2,
```


implies


```math
\beta\le\delta+6, \qquad \gamma\le\delta+6.
```


These are the elementary numerical bounds used in the finiteness argument.

#### Proposition 5.5 — equation (5.2)

Lean checks the positivity implication coming from


```math
\frac{\delta h}{abc} = 1-\frac1p-\frac1q-\frac1r.
```

Equation **(5.2)**.


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
(tA-1)(tB-1) = t(\delta+1)+1.
```


For L2F,


```math
tAB=A+B+\delta
```


gives


```math
(tA-1)(tB-1) = t\delta+1.
```


For FFF, writing


```math
\alpha=A+1,
```


the Table 3 equation


```math
(A+1)\beta\gamma -(A+1)\beta -(A+1)\gamma -\beta\gamma = \delta
```


is transformed into


```math
\bigl(A(\beta-1)-1\bigr) \bigl(A(\gamma-1)-1\bigr) = A\delta+(A+1)^2.
```


This is the completed-product identity used for the FFF divisor
parametrization.

Lean also verifies the recovery-integrality step


```math
U\equiv -1\pmod t
```


in the natural-number form


```math
U\bmod t=(t-1)\bmod t, \qquad t>0,
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
\gcd(\beta\gamma,\alpha\gamma,\alpha\beta)=1 \iff \gcd(\alpha,\beta)= \gcd(\beta,\gamma)= \gcd(\gamma,\alpha)=1.
```


Thus primitivity is equivalent to pairwise coprimality of


```math
\alpha,\beta,\gamma.
```


#### C2F

For the weights


```math
\bigl( B(t+1),\, (A+1)(t+1),\, (A+1)(B+1) \bigr),
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
\bigl( B(t+1),\, A(t+1),\, AB+A+B \bigr),
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
\bigl( B(t+1)+1,\, t(A+1),\, (A+1)(B+1) \bigr),
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
w_1=B(t+1)+1,\qquad w_2=t(A+1)+1,\qquad w_3=A(B+1)+1.
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
\gcd(w_1,w_2,w_3) = \gcd(m-1,w_1).
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
\mathrm{FFF}: \qquad (a,b,c;h) = (\beta\gamma,\alpha\gamma,\alpha\beta;\alpha\beta\gamma),
```



```math
\mathrm{C2F}: \qquad (a,b,c;h) = (\gamma(\beta-1),\alpha\gamma,\alpha\beta;\alpha\beta\gamma),
```



```math
\mathrm{L2F}: \qquad (a,b,c;h) = (\gamma(\beta-1),\gamma(\alpha-1),\alpha\beta-1; \gamma(\alpha\beta-1)),
```



```math
\mathrm{C3}: \qquad (a,b,c;h) = (\beta\gamma-\gamma+1,\alpha(\gamma-1),\alpha\beta; \alpha\beta\gamma),
```


and


```math
\mathrm{L3}: \qquad (a,b,c;h) = (\beta\gamma-\gamma+1,\alpha\gamma-\alpha+1, \alpha\beta-\beta+1;\alpha\beta\gamma+1).
```


Lean first independently reproduces


```math
(N_2,N_3,N_4,N_5,N_6) = (6,8,8,21,0).
```


For δ = 2, the six canonical systems obtained by the enumeration are


```math
\begin{aligned} &(3,5,5;15),\\ &(3,5,7;17),\\ &(3,5,10;20),\\ &(3,7,9;21),\\ &(3,7,12;24),\\ &(3,10,15;30). \end{aligned}
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
(6,8,19;38), \qquad z^2+xy^4+x^5y,
```



```math
(4,7,16;32), \qquad z^2+xy^4+zx^4,
```



```math
(4,7,12;28), \qquad xz^2+y^4+x^4z,
```


and


```math
(4,7,9;25), \qquad yz^2+x^4z+xy^3.
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
