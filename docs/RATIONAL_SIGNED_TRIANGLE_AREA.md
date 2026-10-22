# Rational signed triangle area under general linear maps

The active scope is the rational coordinate plane, its dot product, and signed triangle area. The broader geometry and sector-area foundation proposal is deferred.

For rational points $P,Q,R$, retain the existing signed twice-area

$$
D(P,Q,R)=(Q_x-P_x)(R_y-P_y)-(Q_y-P_y)(R_x-P_x),
$$

and put $A(P,Q,R)=D(P,Q,R)/2$. Reversing two vertices reverses the sign; no orientation restriction is imposed on the triangle.

Let

$$
M=\begin{pmatrix}a&b\\c&d\end{pmatrix},
\qquad a,b,c,d\in\mathbb Q,
\qquad F(X)=MX+t,
\qquad t\in\mathbb Q^2.
$$

The transformation law is

$$
A(F(P),F(Q),F(R))=\det(M)\,A(P,Q,R).
$$

This is the general linear transformation law. On $\mathrm{GL}_2(\mathbb Q)$ the determinant is nonzero; the same theorem holds for all rational matrices, including singular ones. Translations cancel in the edge differences.

## Proof from the existing triangle formula

Write $u=Q-P$ and $v=R-P$. Direct expansion gives

$$
\begin{aligned}
\det(Mu,Mv)
&=(au_x+bu_y)(cv_x+dv_y)
 -(cu_x+du_y)(av_x+bv_y)\\
&=(ad-bc)(u_xv_y-u_yv_x).
\end{aligned}
$$

Dividing by $2$ proves the area law. No distance, angle, quarter-turn or curved-region area property is required.

Consequently:

- If $\det M=1$, signed area is invariant: the $\mathrm{SL}_2(\mathbb Q)$ case.
- If $\det M=-1$, signed area is negated.
- If $\det M=0$, the image triangle has signed area zero.
- Composition is consistent because $\det(MN)=\det(M)\det(N)$.

For example, a shear preserves the area of the oriented unit triangle, the diagonal map with entries $2,3$ multiplies it by $6$, and swapping coordinates reverses its sign.

## The dot product remains a separate rational operation

The corresponding exact dot-product formula is

$$
(Mu)\mathbin{\cdot}(Mv)=u\mathbin{\cdot}(M^{\mathsf T}Mv).
$$

Thus general linear maps act on signed area through the determinant, while their effect on the dot product is described by $M^{\mathsf T}M$. No area transformation rule needs to be assumed from dot-product invariance.

## Formalization

`RationalTriangleAreaTransform.lean` uses the existing `PiCirclePoint` and `RationalCircle.triangleTwiceArea`, with rational matrix entries. Its `triangleSignedArea_affine` theorem proves the displayed law for arbitrary matrices, translations and vertices. `triangleTwiceArea_affine` preserves the existing doubled-area API. The determinant-one, singular and coordinate-swap laws are corollaries. Matrix composition, determinant multiplication and the dot-product formula are checked as well.

The checker audits these theorem dependencies and includes exact rational examples of a shear, a positive-determinant scaling, an orientation reversal and a singular map. The proof bundle records the exact dependency sources and the verification result. It is an opt-in companion, with no change to the main library root's exports.

Read the [checked module](../book/rational-signed-triangle/proof/ComputableAnalysis/RationalTriangleAreaTransform.lean), [checker output](../book/rational-signed-triangle/proof/verification/check.log), or [reproduction instructions](../book/rational-signed-triangle/proof/README.md).
