import ComputableAnalysis.NBallGaussian
import ComputableAnalysis.Pi

open ComputableAnalysis

#print axioms nBallCoeff_mul_gammaHalfCoeff
#print axioms nBallVolumeModel_gamma
#print axioms gaussian_square_split
#print axioms gaussian_diagonal_bound
#print axioms NBallRaw.volume_valid
#print axioms NBallRaw.volume_equiv
#print axioms nBallVolumeModelInterval_contains

example : gammaHalfCoeff 7 = 105 / 16 := by native_decide
example : nBallCoeff 7 = 16 / 105 := by native_decide
example : gaussianTriangleSum [1,2,3] = 11 := by native_decide
example : gaussianDiagonalSum [1,2,3] = 14 := by native_decide
example : (NBallRaw.volume 3 (RealRaw.ofRat (22/7)) (RealRaw.ofRat (3/2))).Valid :=
  NBallRaw.volume_valid 3 _ _ (RealRaw.ofRat_valid _) (RealRaw.ofRat_valid _)
    (fun _ => by change (0 : Rat) ≤ 22/7; grind)
    (fun _ => by change (0 : Rat) ≤ 3/2; grind)

-- Exact runtime fixtures for the independently implemented browser calculator.
#eval do
  for stage in [1,2,4,8] do
    let p := piMachin.compute stage
    IO.println ("PI|" ++ toString stage ++ "|" ++ toString p.lo ++ "|" ++ toString p.hi)
    for n in [0,1,2,3,5,7,12,20,64] do
      for r in [(0 : Rat), 1/2, 1, 3/2] do
        let v := nBallVolumeModelInterval n p ⟨r,r⟩
        IO.println ("BALL|" ++ toString stage ++ "|" ++ toString n ++ "|" ++
          toString r ++ "|" ++ toString v.lo ++ "|" ++ toString v.hi)
  for n in List.range 65 do
    IO.println ("COEFF|" ++ toString n ++ "|" ++ toString (nBallCoeff n) ++ "|" ++
      toString (gammaHalfCoeff n))
