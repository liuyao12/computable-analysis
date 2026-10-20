import ComputableAnalysis.Basic

/-!
# Extending rational-input functions to computable reals

A function known only on rational inputs extends to computable reals when it
comes with an effective modulus: to compute the output to precision `eps`, it is
enough to know the input inside some rational radius `delta eps`.

This is the constructive replacement for the usual appeal to density of `Q` in
`R` plus continuity.
-/

namespace ComputableAnalysis

/-- Rational-input function with an effective modulus of continuity.

`raw` computes an interval for `f q`.  `modulus eps` is the input precision
needed to make outputs at nearby rational inputs agree at scale `eps`.
-/
structure UniformRealFun where
  raw : RealFunRaw
  rawValid : raw.Valid
  modulus : Nat -> Nat
  uniform : forall x y n,
    qabs (x - y) <= 1 / ((modulus n : Nat) : Rat) ->
    QInterval.Overlaps (raw.compute x n) (raw.compute y n)

/-- A partial rational-input algorithm with a validity proof on its domain. -/
structure PartialRealFun where
  raw : PartialRealFunRaw
  rawValidOnDomain : forall x h, RealRaw.ValidCompute (raw.compute x h)

namespace UniformRealFun

/-- Extend a uniformly continuous rational-input function to a raw real-input
algorithm.

To compute `f(x)` at tolerance `eps`, approximate `x` at the modulus scale,
take the midpoint rational, and evaluate the rational-input algorithm there.
The theorem that this is independent of representative is the next proof
obligation.
-/
def extendCompute (f : UniformRealFun) (x : RealRaw) : Nat -> QInterval :=
  fun n =>
    let delta := f.modulus n
    let q := (x.compute delta).midpoint
    f.raw.compute q n

def extensionRespectsEquiv (f : UniformRealFun) : Prop :=
  forall x y : RealRaw,
    x.Valid ->
    y.Valid ->
    x.Equiv y ->
    forall eps, QInterval.Overlaps (extendCompute f x eps) (extendCompute f y eps)

def extensionValid (f : UniformRealFun) : Prop :=
  forall x : RealRaw, x.Valid -> RealRaw.ValidCompute (extendCompute f x)

/-- A certified extension theorem packages the two facts needed to respect the
project's real-representation equivalence. -/
structure CertifiedExtension (f : UniformRealFun) where
  valid : extensionValid f
  respectsEquiv : extensionRespectsEquiv f

def CertifiedExtension.extendRaw {f : UniformRealFun} (_cert : CertifiedExtension f)
    (x : RealRaw) (_hx : x.Valid) : RealRaw where
  compute := extendCompute f x

end UniformRealFun

end ComputableAnalysis
