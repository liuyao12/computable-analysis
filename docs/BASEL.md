# Basel and the Euler-product proof of prime infinitude

`Basel.eulerBasel` proves $\zeta(2)=\pi^2/6$ as `RealRaw.Equiv`, using the
existing geometric `piCircleArea` and the independently defined reciprocal-square
series. `Basel.real_zeta_two_equiv_piSquaredOverSix` identifies the value of the
public `ZetaReal.zeta` function at $2$ with the same right-hand side.

The proof is unconditional. It imports project modules only and introduces no
completed real numbers, axioms, proof placeholders, or native-decision shortcuts.
Its geometric dependency retains the foundation's previously audited native
axioms; this is not a claim that the whole dependency closure is axiom-free.

## The finite Basel estimate

Write

$$
B_N=\sum_{k<N}\frac{(-1)^k}{2k+1},\qquad
H_N=\sum_{k<N}\frac1{2k+1},\qquad
M_N=\sum_{k<N}\frac1{(2k+1)^2}.
$$

The finite square of the Leibniz sum can be split into diagonals or compared
with its triangular truncation $T_N$. Partial fractions and alternating-sum
bounds prove

$$
|B_N^2+T_N-M_N|\le H_N/N,\qquad
|B_N^2-T_N|\le H_N/N.
$$

Thus $|2B_N^2-M_N|\le2H_N/N$. The odd/even decomposition of reciprocal squares,
together with the already proved tail bound, yields

$$
\left|\sum_{k=1}^{2m^2}k^{-2}-\frac83B_{2m^2}^{\,2}\right|\le\frac{16}{m}
\quad(m\ge1).
$$

The estimate compares lower endpoints of refined interval computations. Any
positive rational separation between the two computations is contradicted by
this explicit schedule. The existing Leibniz-to-geometric-pi equivalence then
proves Basel. The method adapts the rearrangement proof of
[Benko and Molokach (2013)](https://doi.org/10.4169/college.math.j.44.3.171),
with all rearrangements finite and each limiting step replaced by an error bound.

## The finite Euler sieve

For a list $P$ of distinct primes, define

$$
c_P=\prod_{p\in P}(1-p^{-2}),\qquad
S_P(N)=\sum_{\substack{1\le k\le N\\\forall p\in P,\ p\nmid k}}k^{-2}.
$$

For a new prime $p\notin P$, `EulerSieve.sieve_cons` proves the exact identity

$$
S_{p::P}(N)=S_P(N)-p^{-2}S_P(\lfloor N/p\rfloor).
$$

`EulerSieve.sieve_error` proves

$$
\left|S_P(N)-c_P\sum_{k=1}^N k^{-2}\right|\le\frac{K_P}{N+1},\qquad
K_{\varnothing}=0,\quad K_{p::P}=(p+1)K_P+2p.
$$

An exhaustive prime list would make $S_P(N)=1$ for $N\ge1$, hence
$\zeta(2)=1/c_P\in\mathbb Q$. Basel would then make $\pi^2$ rational.

`Basel.prime_unbounded_of_piSquare_irrational` consequently proves

$$
\pi^2\notin\mathbb Q\quad\Longrightarrow\quad
\forall N\in\mathbb N,\ \exists p>N,\ p\text{ prime}.
$$

**Irrationality of $\pi^2$ remains a hypothesis.** Irrationality of $\pi$ alone
is insufficient. The general formulas for $\zeta(2n)$ beyond Basel remain open.

## Verification

Run `lake build ComputableAnalysis.Basel.RealZeta`, then
`lake env lean scripts/check_basel.lean` and `lake env lean scripts/check_zeta_real.lean`.
The first audit traverses elaborated proofs: it requires the finite Basel
comparison and Euler sieve, rejects the existing Euclidean infinitude theorems,
and rejects unfinished proofs and new Basel axioms. The second lists the
axioms inherited by the public theorems, alongside the real-zeta audit.
