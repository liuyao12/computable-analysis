# Factorial rotation and Peano–Baker

`ComputableAnalysis/RotationPeanoBakerBridge.lean` records the finite core of
the long Euler/ODE route.

For every rational time (T) and finite stage (n), the complex factorial
center used by `RotationSeries.rotationCenter` is simultaneously:

- the even partial sum of the complex exponential at (iT); and
- the cosine/sine form of the constant-coefficient Peano–Baker matrix partial
  sum for the rotation generator.

The key declarations are:

- `RotationPeanoBakerBridge.rotationCenter_eq_expPartial`
- `RotationPeanoBakerBridge.rotationCenter_eq_constantPeanoBakerPartial`

This is deliberately a finite rational identity.  It does not claim a
continuous ODE solution, identify the represented-angle rotation with a
geometric circle point, or establish Euler’s identity.  Those are the next
analytic and geometric certificates needed to close the route.
