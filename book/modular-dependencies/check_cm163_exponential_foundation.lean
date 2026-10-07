import ComputableAnalysis.ModularForms.CMExponentialFoundation163
open ComputableAnalysis ComputableAnalysis.ModularForms.EC163

#check input
#check complex_exp_agreement
#check real_exp_agreement
#check implementation_agreement
#check deficit_agreement
#check deficit_bounds
#check exp_bounds
#check compoundInterest_bounds
#check linearODE_bounds

#print axioms complex_exp_agreement
#print axioms real_exp_agreement
#print axioms implementation_agreement
#print axioms deficit_agreement
#print axioms deficit_bounds
#print axioms exp_bounds
#print axioms compoundInterest_bounds
#print axioms linearODE_bounds

/-- Regression: arbitrary equivalent names of the irrational input retain
the same bound, with the implementation selected by the application. -/
example (f : ExponentialComputations.Implementation) (x : ExponentialComputations.RealInput)
    (hx : x.val.Equiv input.val) :
    (RealRaw.ofRat (1/100000000000000)).Le (deficit f x) ∧
      (deficit f x).Le (RealRaw.ofRat (9/10000000000000)) := deficit_bounds f x hx
