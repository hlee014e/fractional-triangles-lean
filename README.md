# Fractional Triangles — Lean Verification

Lean 4 verification accompanying the *Fractional Triangles* manuscript.

All files compile with

```bash
lake build
```

without `sorry`.

---

## Lemma 4.2

Let

\[
L=L(p,q,r)
=
\langle x,y,z,c
\mid
px=qy=rz=c
\rangle ,
\]

and

\[
\omega=c-x-y-z,
\qquad
\delta\tau=\omega.
\]

For the three stacky points

\[
G_1\simeq B\mu_p,\qquad
G_2\simeq B\mu_q,\qquad
G_3\simeq B\mu_r,
\]

consider the character maps

\[
\chi_1:L\to\mathbf Z/p\mathbf Z,
\qquad
\chi_2:L\to\mathbf Z/q\mathbf Z,
\qquad
\chi_3:L\to\mathbf Z/r\mathbf Z.
\]

### Character computation

**Lean files**

- `FractionalTriangles/Grading.lean`
- `FractionalTriangles/Section4_Lemma42Characters.lean`

Lean constructs the maps from the quotient presentation of \(L(p,q,r)\) and verifies

\[
\begin{array}{c|cccc}
 &x&y&z&c\\ \hline
\chi_1&1&0&0&0\\
\chi_2&0&1&0&0\\
\chi_3&0&0&1&0
\end{array}
\]

and hence

\[
\chi_i(\omega)
=
\chi_i(c-x-y-z)
=
-1.
\]

If

\[
s_i:=\chi_i(\tau),
\]

then

\[
\delta\tau=\omega
\]

implies

\[
\boxed{\delta s_i=-1\pmod {p_i}}.
\]

Therefore

\[
\boxed{\gcd(s_i,p_i)=1}.
\]

In particular,

\[
ms_i=0\pmod {p_i}
\quad\Longrightarrow\quad
p_i\mid m.
\]

---

### Fiber character at \(G_i\)

**Lean file**

- `FractionalTriangles/Section4_Lemma42Fiber.lean`

For

\[
L^m|_{G_i},
\]

the fiber character is

\[
ms_i\in\mathbf Z/p_i\mathbf Z.
\]

The elementary invariant-vector calculation formalized in Lean is

\[
a\neq1,\qquad av=v
\quad\Longrightarrow\quad
v=0.
\]

Together with the standard identification

\[
H^0(B\mu_{p_i},V)=V^{\mu_{p_i}},
\]

this gives

\[
H^0(G_i,L^m|_{G_i})
=
\begin{cases}
\mathbf C,& ms_i=0,\\[2mm]
0,& ms_i\neq0.
\end{cases}
\]

Since \(s_i\) is a unit,

\[
ms_i=0
\iff
p_i\mid m.
\]

Thus

\[
\boxed{
H^0(G_i,L^m|_{G_i})\neq0
\iff
p_i\mid m.
}
\]

The identification

\[
H^0(B\mu_p,V)=V^{\mu_p}
\]

is used as a standard external stack-theoretic input.

---

### Evaluation and Serre vanishing

Let \(I_i\) be the ideal sheaf of \(G_i\). The geometric exact sequence is

\[
0
\longrightarrow I_iL^m
\longrightarrow L^m
\longrightarrow L^m|_{G_i}
\longrightarrow0.
\]

Hence

\[
H^0(X,L^m)
\longrightarrow
H^0(G_i,L^m|_{G_i})
\longrightarrow
H^1(X,I_iL^m).
\]

Therefore

\[
H^1(X,I_iL^m)=0
\]

implies

\[
H^0(X,L^m)
\twoheadrightarrow
H^0(G_i,L^m|_{G_i}).
\]

For

\[
p_i\mid m,\qquad m\gg0,
\]

this gives

\[
\exists s\in H^0(X,L^m),
\qquad
s|_{G_i}\neq0,
\]

and consequently

\[
\boxed{m\in\Sigma_{P_i}}.
\]

---

### Finite residue classes

**Lean file**

- `FractionalTriangles/Section4_Lemma42Serre.lean`

For \(M>0\),

\[
m=qM+r,
\qquad
0\le r<M.
\]

Lean verifies the finite-residue deduction

\[
\left[
\forall r<M,\;
\exists Q_r,\;
q\ge Q_r\Rightarrow P(q,r)
\right]
\]

\[
\Longrightarrow
\]

\[
\boxed{
\exists Q,\;
\forall r<M,\;
q\ge Q\Rightarrow P(q,r).
}
\]

This is the finite arithmetic step used after applying Serre vanishing in the finitely many residue classes modulo \(M\).

Serre vanishing itself and the coarse-space projection/cohomology comparison are external geometric inputs.

---

### Computation of \(\gcd(\Sigma_{P_i})\)

**Lean file**

- `FractionalTriangles/Section4_Lemma42.lean`

The two directions are

\[
m\in\Sigma_{P_i}
\quad\Longrightarrow\quad
p_i\mid m,
\]

and, for \(m\gg0\),

\[
p_i\mid m
\quad\Longrightarrow\quad
m\in\Sigma_{P_i}.
\]

Thus for some sufficiently large \(K\),

\[
p_iK,\;
p_i(K+1),\;
p_i(K+2),\ldots
\in\Sigma_{P_i}.
\]

Lean verifies

\[
\gcd\bigl(p_iK,p_i(K+1)\bigr)
=
p_i\gcd(K,K+1)
=
p_i.
\]

Since

\[
p_i\mid m
\qquad
(\forall m\in\Sigma_{P_i}),
\]

it follows that

\[
\boxed{
\gcd(\Sigma_{P_i})=p_i.
}
\]

Consequently, using the stacky-Proj stabilizer formula,

\[
\operatorname{Stab}(P_i)
=
\mu_{\gcd(\Sigma_{P_i})}
=
\boxed{\mu_{p_i}}.
\]

---

## Formalization boundary for Lemma 4.2

The Lean files verify the concrete algebraic/arithmetic chain

\[
\delta\tau=\omega
\]

\[
\Downarrow
\]

\[
\delta s_i=-1
\]

\[
\Downarrow
\]

\[
s_i\in(\mathbf Z/p_i\mathbf Z)^\times
\]

\[
\Downarrow
\]

\[
ms_i=0
\iff
p_i\mid m
\]

together with

\[
\text{finite-residue eventuality}
\]

and

\[
\text{eventual }p_i\text{-multiples in }\Sigma_{P_i}
\Longrightarrow
\gcd(\Sigma_{P_i})=p_i.
\]

The following standard geometric results are presently external inputs:

\[
L(p,q,r)\simeq\operatorname{Pic}(X),
\]

\[
G_i\simeq B\mu_{p_i},
\]

\[
\operatorname{Pic}(B\mu_{p_i})
\simeq
\operatorname{Hom}(\mu_{p_i},\mathbf C^*)
\simeq
\mathbf Z/p_i\mathbf Z,
\]

\[
H^0(B\mu_p,V)=V^{\mu_p},
\]

\[
0\to I_iL^m\to L^m\to L^m|_{G_i}\to0,
\]

the coarse-space projection/cohomology comparison,

\[
H^1(X,I_iL^m)=0
\qquad (m\gg0)
\]

in the required residue classes, and the final stacky-Proj reconstruction/normalization theorem.

---

## Build status

\[
\boxed{\texttt{lake build}\quad\text{completed successfully}}
\]

for the current project.
### Polarization and faithful character

\[
S_m=T_{m\tau},
\qquad
S_1=T_\tau.
\]

Hence degree \(1\) in the section-ring grading corresponds to
\(\tau\) in the \(L(p,q,r)\)-grading:

\[
1\longleftrightarrow\tau.
\]

For

\[
Y=\operatorname{Proj}^{st}S,
\]

the geometric identification is

\[
f^*\mathcal O_Y(1)\simeq\mathcal O_X(\tau).
\]

Thus at the \(i\)-th stacky point,

\[
\operatorname{char}_{P_i}\mathcal O_Y(1)
=
s_i
=
\chi_i(\tau).
\]

Lean verifies

\[
\delta\tau=\omega
\]

\[
\Downarrow
\]

\[
\delta s_i=-1
\]

\[
\Downarrow
\]

\[
s_i\in(\mathbf Z/p_i\mathbf Z)^\times
\]

\[
\Downarrow
\]

\[
\chi_{s_i}:\mu_{p_i}\to\mathbf C^*
\quad\text{is faithful}.
\]

It also verifies the group-theoretic implication

\[
\boxed{
\text{faithful pulled-back }\mathcal O(1)
\Longrightarrow
\text{injective stabilizer map}.
}
\]

The subsequent implication

\[
\text{injective stabilizer maps}
\Longrightarrow
f\text{ representable}
\]

is the standard representability criterion for morphisms of
Deligne--Mumford stacks and is presently an external geometric input.
The remaining stack-theoretic reconstruction uses

\[
L^M=\pi^*\bar L
\]

for sufficiently divisible \(M\), ordinary Proj reconstruction on the
coarse \(\mathbf P^1\),

\[
X_{\mathrm{coarse}}\simeq Y_{\mathrm{coarse}},
\]

the representability criterion,

\[
\text{proper}+\text{quasifinite}
\Longrightarrow
\text{finite},
\]

and

\[
\text{finite representable birational}
+
\text{normal target}
\Longrightarrow
\text{isomorphism}.
\]

These stack-theoretic results are presently external inputs.
