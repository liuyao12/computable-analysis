import Lake
open Lake DSL
package rationalGeometry
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "51e6992efd06126df61a496bebf8f49482a4e129"
@[default_target]
lean_lib RationalGeometry where
  roots := #[`RationalProofAudit, `RationalConvexBodies, `RationalSimplexLinearAlgebra]
