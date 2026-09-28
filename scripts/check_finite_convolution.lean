import ComputableAnalysis.FiniteConvolution

open ComputableAnalysis
open ComputableAnalysis.FiniteProbabilityKernel

namespace FiniteConvolutionChecks

def coin : FiniteProbabilityKernel where
  samples := [⟨-1, 1/2⟩, ⟨1, 1/2⟩]
  weights_nonnegative := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h <;> subst s <;> native_decide
  totalWeight_eq_one := by native_decide

def sparse : FiniteProbabilityKernel where
  samples := [⟨-2, 1/8⟩, ⟨0, 3/4⟩, ⟨2, 1/8⟩]
  weights_nonnegative := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h <;> subst s <;> native_decide
  totalWeight_eq_one := by native_decide

-- Nontrivial runtime regression: two encodings with the same first two
-- moments but different fourth moments must not be identified as laws.
theorem matched_moments : coin.mean = sparse.mean ∧
    coin.secondMoment = sparse.secondMoment := by native_decide

theorem fourth_moments_differ :
    coin.action (fun x => x*x*x*x) = 1 ∧
    sparse.action (fun x => x*x*x*x) = 4 := by native_decide

theorem cubic_budgets : coin.thirdAbsoluteMoment = 1 ∧
    sparse.thirdAbsoluteMoment = 2 := by native_decide

theorem four_coin_sum :
    (coin.convolutionPower 4).mean = 0 ∧
    (coin.convolutionPower 4).variance = 4 ∧
    (coin.convolutionPower 4).action (fun x => x*x*x*x) = 40 := by native_decide

theorem rescaled_four_coin_sum :
    (coin.convolutionPower 4).action (fun x => (x/2)*(x/2)) = 1 := by native_decide

-- Association and commutation compare actions even when list order differs.
example (f : Rat → Rat) :
    (coin.convolution sparse).action f = (sparse.convolution coin).action f :=
  WeightedPoint.action_convolution_comm _ _ _

example (f : Rat → Rat) :
    ((coin.convolution sparse).convolution coin).action f =
      (coin.convolution (sparse.convolution coin)).action f :=
  WeightedPoint.action_convolution_assoc _ _ _ _

-- A cubic perturbation has the predicted bound without using an integral.
example : qabs (coin.action (fun x => 3 + 2*x + x*x + x*x*x) -
    sparse.action (fun x => 3 + 2*x + x*x + x*x*x)) ≤
      coin.thirdAbsoluteMoment + sparse.thirdAbsoluteMoment := by
  have h := cubic_replacement_bound coin sparse matched_moments.1 matched_moments.2
    (fun x => 3 + 2*x + x*x + x*x*x) 3 2 1 1
    (by
      intro s hs
      have he : (3 + 2*s.point + s.point*s.point + s.point*s.point*s.point) -
          (3 + 2*s.point + 1*(s.point*s.point)) = s.point*s.point*s.point := by grind
      rw [he, qabs_mul, qabs_mul, Rat.one_mul]
      exact Rat.le_refl)
    (by
      intro s hs
      have he : (3 + 2*s.point + s.point*s.point + s.point*s.point*s.point) -
          (3 + 2*s.point + 1*(s.point*s.point)) = s.point*s.point*s.point := by grind
      rw [he, qabs_mul, qabs_mul, Rat.one_mul]
      exact Rat.le_refl)
  simpa only [Rat.one_mul] using h

end FiniteConvolutionChecks

#print axioms WeightedPoint.action_convolution
#print axioms WeightedPoint.action_convolution_comm
#print axioms WeightedPoint.action_convolution_assoc
#print axioms FiniteProbabilityKernel.variance_convolution
#print axioms FiniteProbabilityKernel.cubic_replacement_bound
#print axioms FiniteProbabilityKernel.convolutionPower_replacement_bound
#print axioms FiniteProbabilityKernel.scaled_convolutionPower_cubic_bound
