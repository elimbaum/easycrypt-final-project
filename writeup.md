need to make sure this is constrained, not too much work, actually can do something. also, make sure [[HKO+18]] didn't already do this!

- talk to nicolas about ideas?

I think settling on [[Fantastic Four]] Multiplication verification.

Next steps:
1. Email Alley/Marco about protocols
2. Look at MP-SPDZ implementation

# ideas
matrix representation? is it too redundant, or sufficiently easy to work with?

*Valid sharing:*
- All diagonals are 0 (represent with `.`, or maybe just use a symbol?)
- The nonzero values of each column are all $[x]_i$
- The sum of the entire matrix is $3x$ (...3 copies of each share)

Sufficient?

Each party can view one *row* of the matrix.

`JMP` takes a value known by two parties and sends it to another.
$$
\mathsf{JMP}(x, (P_1, P_2)\rightarrow P_3):\left[\begin{matrix}
. & 0 & 0 & x \\
0 & . & 0 & x \\
0 & 0 & . & ? \\
0 & 0 & 0 & . \\
\end{matrix}\right] \rightarrow
\left[\begin{matrix}
. & 0 & 0 & x \\
0 & . & 0 & x \\
0 & 0 & . & x \\
0 & 0 & 0 & . \\
\end{matrix}\right]
$$
Note that the left matrix is *not* a valid sharing. However, we do need some sort of constraint that parties 1 and 2 agree on shares.

`INP` takes a value known by two parties and secret shares it among all parties.
$$
\mathsf{INP}(x, P_1, P_2):\left[\begin{matrix}
. & 0 & 0 & x \\
0 & . & 0 & x \\
0 & 0 & . & ? \\
0 & 0 & 0 & . \\
\end{matrix}\right] \rightarrow
\left[\begin{matrix}
. & 0 & r & x-r \\
0 & . & r & x-r \\
0 & 0 & . & x-r \\
0 & 0 & r & . \\
\end{matrix}\right]
$$
where $r=\mathsf{PRG}(K_3)$ . Again, the left / input matrix is not a valid sharing, but the output is. This is secure, because $P_1, P_2$'s view is $r+(x-r)=x$, which they already knew. $P_3$'s view is $x-r$, uniformly random, and $P_4$ gets only $r$.

`MULT` calls `INP` multiple times.

For each combined step:
- $P_i,P_j$ call $\mathsf{INP}(x_gy_h + x_hy_g)$
- everyone adds together what they receive

Example: $P_1,P_2$ call $\mathsf{INP}(x_3y_4+x_4y_3)$.
$$
\mathsf{INP}(x_3y_4+x_4y_3, P_1, P_2):\left[\begin{matrix}
. & 0 & 0 & x_3y_4+x_4y_3 \\
0 & . & 0 & x_3y_4+x_4y_3 \\
0 & 0 & . & ? \\
0 & 0 & 0 & . \\
\end{matrix}\right] \rightarrow
\left[\begin{matrix}
. & 0 & r_3 & x_3y_4+x_4y_3-r_3 \\
0 & . & r_3 & x_3y_4+x_4y_3-r_3 \\
0 & 0 & . & x_3y_4+x_4y_3-r_3 \\
0 & 0 & r_3 & . \\
\end{matrix}\right]
$$
where $r_3=\mathsf{PRG}(K_3)$, a random value that only $P_3$ *doesn't* know.

`INPLocal`...
$$
\mathsf{INPLocal}(x, P_1, P_2, P_3):\left[\begin{matrix}
. & 0 & 0 & x \\
0 & . & 0 & x \\
0 & 0 & . & x \\
0 & 0 & 0 & . \\
\end{matrix}\right]
$$
...is entirely local.

---

```
INP(x, Pi, Pj):
	Env.INPa(x, all parties)
	Pi.INPa(x, Pj, Pg, Ph) // Pi's half of INP, sends to Pg, Ph
		// Ph.gen_random()
	Pj.INPb(x, Pi, Pg, Ph) // Pj's half of INP, sends to Pg, Ph
		// Pg.updateMatrix(whatever)

JMP(x, Pi, Pj, Pg):
```

`row 3, row 4 ~ uniform`

---
# multiplication

Need to run
- $\mathsf{INP}(x_3y_4+x_4y_3, P_1, P_2)$
- $\mathsf{INP}(x_2y_4+x_4y_2, P_1, P_3)$
- $\mathsf{INP}(x_3y_2+x_2y_3, P_1, P_4)$
- $\mathsf{INP}(x_1y_4+x_4y_1, P_2, P_3)$
- $\mathsf{INP}(x_3y_1+x_1y_3, P_2, P_4)$
- $\mathsf{INP}(x_2y_1+x_1y_2, P_3, P_4)$

That's a total of 6 calls. 2 parties participate in each, so each party participates in 3.

In general, $P_i$ takes part in
- $\mathsf{INP}(x_gy_h+x_hy_g, P_i, P_j)$
- $\mathsf{INP}(x_jy_h+x_hy_j, P_i, P_g)$
- $\mathsf{INP}(x_gy_j+x_jy_g, P_i, P_h)$

But with our matrix representation of parties, we just run all six.

This gives six matrices, which we add together. Then incorporate $\mathsf{INPLocal}(x_g y_g)$ matrices.

The combined diagonal-entry matrix, $\sum_i [x_i y_i]$, is
$$
\left[
\begin{matrix}
. & x_2y_2 & x_3y_3 & x_4y_4 \\
x_1y_1 & . & x_3y_3 & x_4y_4 \\
x_1y_1 & x_2y_2 & . & x_4y_4 \\
x_1y_1 & x_2y_2 & x_3y_3 & .
\end{matrix}
\right]
$$
All together now...
$$
\begin{align*}
\left[\begin{matrix}
. & 0 & r_{34} & x_3y_4+x_4y_3-r_{34} \\
0 & . & r_{34} & x_3y_4+x_4y_3-r_{34} \\
0 & 0 & . & x_3y_4+x_4y_3-r_{34} \\
0 & 0 & r_{34} & . \\
\end{matrix}\right]
&+
\left[\begin{matrix}
. & r_{24} & 0 & x_2y_4+x_4y_2-r_{24} \\
0 & .   & 0 & x_2y_4+x_4y_2-r_{24} \\
0 & r_{24} & . & x_2y_4+x_4y_2-r_{24} \\
0 & r_{24} & 0 & . \\
\end{matrix}\right]
\\\\
+
\left[\begin{matrix}
. & 0 & 0 & x_1y_4+x_4y_1-r_{14} \\
r_{14} & .   & 0 & x_1y_4+x_4y_1-r_{14} \\
r_{14} & 0 & . & x_1y_4+x_4y_1-r_{14} \\
r_{14} & 0 & 0 & . \\
\end{matrix}\right]
& +
\left[\begin{matrix}
. & r_{23} & x_2y_3+x_3y_2-r_{23} & 0 \\
0 & .   & x_2y_3+x_3y_2-r_{23} & 0 \\
0 & r_{23} & . & 0 \\
0 & r_{23} & x_2y_3+x_3y_2-r_{23} & . \\
\end{matrix}\right]
\\\\
+
\left[\begin{matrix}
. & 0 & x_1y_3+x_3y_1-r_{13} & 0 \\
r_{13} & .   & x_1y_3+x_3y_1-r_{13} & 0 \\
r_{13} & 0 & . & 0 \\
r_{13} & 0 & x_1y_3+x_3y_1-r_{13} & . \\
\end{matrix}\right]
&+
\left[\begin{matrix}
. & x_1y_2+x_2y_1-r_{12} & 0 & 0 \\
r_{12} & .   & 0 & 0 \\
r_{12} & x_1y_2+x_2y_1-r_{12} & . & 0 \\
r_{12} & x_1y_2+x_2y_1-r_{12} & 0 & . \\
\end{matrix}\right]
\\\\
&+
\left[
\begin{matrix}
. & x_2y_2 & x_3y_3 & x_4y_4 \\
x_1y_1 & . & x_3y_3 & x_4y_4 \\
x_1y_1 & x_2y_2 & . & x_4y_4 \\
x_1y_1 & x_2y_2 & x_3y_3 & .
\end{matrix}
\right]
\end{align*}
$$
Does this check out?

The **first** share is
$$
r_{14} + r_{13} + r_{12} + x_1y_1
$$
The **second** share is
$$
r_{24}+r_{23}+(x_1y_2+x_2y_1-r_{12})+x_2y_2
$$
The third share is
$$
r_{34}+(x_2y_3+x_3y_2-r_{23})+(x_1y_3+x_3y_1-r_{13})+x_3y_3
$$
The fourth share is
$$
(x_3y_4+x_4y_3-r_{34})+(x_2y_4+x_4y_2-r_{24})+(x_1y_4+x_4y_1-r_{14})+x_4y_4
$$
The total sum of these is
$$
\begin{align*}
r_{14} + r_{13} + r_{12} + x_1y_1 \\
r_{24}+r_{23}+(x_1y_2+x_2y_1-r_{12})+x_2y_2 \\
r_{34}+(x_2y_3+x_3y_2-r_{23})+(x_1y_3+x_3y_1-r_{13})+x_3y_3 \\
\underline{+ (x_3y_3+x_4y_3-r_{34})+(x_2y_4+x_4y_2-r_{24})+(x_1y_4+x_4y_1-r_{14})+x_4y_4} \\
x_1y_1+(x_1y_2+x_2y_1+x_2y_2)+(x_2y_3+x_3y_2+x_1y_3+x_3y_1+x_3y_3)\\
\underline{+(x_3y_4+x_4y_3+x_2y_4+x_4y_2+x_1y_4+x_4y_1+x_4y_4)}\\
x_1(y_1+y_2+y_3+y_4)+x_2(y_1+y_2+y_3+y_4)\\
+x_3(y_1+y_2+y_3+y_4)+x_4(y_1+y_2+y_3+y_4)\\
=x\cdot y
\end{align*}
$$