# Fourier inversion on the line

How can an integral over frequencies recover the value of a function at
one point? The proof begins at the origin. Subtract a Gaussian profile
scaled to match the value of the function there. The difference vanishes
at zero, so division by the spatial variable becomes a calculation with
the fundamental theorem of calculus.

## Divide the difference using the FTC

With a profile \(g\) satisfying \(g(0)=1\), put

$$
h(t)=f(t)-f(0)g(t),\qquad
w(t)=\int_0^1 h'(st)\,ds.
$$

The FTC gives \(tw(t)=h(t)\), including at \(t=0\). The integral defines
the value of the quotient at zero and gives bounds there. Away from
zero, the quotient formula gives decay bounds from those for the original
functions. The checked proof combines these two estimates and constructs
the derivative evidence for the Gaussian-subtracted quotient.

## Differentiate in frequency, then use decay

Frequency differentiation takes multiplication by the spatial variable
to a derivative of the transform. Thus the transform of \(h\) comes from
the derivative of the transform of \(w\), with the scalar and sign fixed
by the Fourier kernel. Integrate over a finite frequency window first.
The boundary terms tend to zero by the proved transform decay, so the
remaining contribution to inversion comes from the Gaussian.

This argument uses dyadic quadratures on compact windows and quantitative
tail estimates for the improper integrals. Lean's entry points include
`FourierQuadrature.lineTransform_frequencyDerivative`,
`lineTransform_spatialDerivative`, `lineTransform_decay_of_derivative`,
and `lineFTCQuotient_fourierIntegral_zero`.

## Fix the normalization and translate the argument

The Gaussian cosine transform is identified exactly at each represented
frequency in `FourierQuadrature.gaussianUnit_cosine_transform_exact`.
The [dyadic Gaussian mass calculation](03a-gaussian-integral.md)
identifies its unscaled mass with \(\sqrt{\pi}\). The remaining inversion
factor is that mass squared divided by \(\pi\), so it is exactly \(1\).

Translation moves the reconstruction from the origin to an arbitrary
valid represented point \(x\). `FourierQuadrature.inverseLineAt_eq`
states the resulting equality of real values. The input is a real-valued
sampler with quantitative derivative, moment, and decay evidence, exposed
as `LineDerivatives` and `LineDecay` together with agreement of the moment
sampler with \(t\mapsto tf(t)\). `inverseLineAt_congr` proves that changing
the name of \(x\) preserves the computed value.

The distribution project supplies these certificates for its one-dimensional
compact test interface with uniform derivative evidence, giving
`ComputableDistributions.CompactFourier.Line.dyadicInverseAt_eq`.
This use of inversion is downstream of the one-dimensional foundation.
