import ComputableAnalysis.RealParameterSample

/-! Elementary bounds and affine operations for represented exponents. -/
namespace ComputableAnalysis.BinomialPower

/-- A rational bound on the initial parameter box; this is quantitative domain
data, not an assumed property of the resulting power or integral. -/
def ParameterBound (p : Real) (C : Rat) : Prop :=
  ∀ s, (p.compute 0).lo ≤ s → s ≤ (p.compute 0).hi → qabs (2-s) ≤ C-1

def parameterBound (p : Real) : Rat := qabs (p.compute 0).lo+qabs (p.compute 0).hi+4

theorem parameterBound_ge (p : Real) : 1 ≤ parameterBound p := by
  have := qabs_nonneg (p.compute 0).lo
  have := qabs_nonneg (p.compute 0).hi
  unfold parameterBound
  grind only

theorem parameterBound_spec (p : Real) : ParameterBound p (parameterBound p) := by
  intro s hlo hhi
  have hl := neg_qabs_le_self (p.compute 0).lo
  have hh := self_le_qabs (p.compute 0).hi
  have hl0 := qabs_nonneg (p.compute 0).lo
  have hh0 := qabs_nonneg (p.compute 0).hi
  unfold parameterBound
  apply qabs_le_of_neg_le_le <;> grind only

def shiftParameter (p : Real) : Real :=
  Real.ofRaw (RealRaw.add p.preferred (RealRaw.ofRat 1))
    (RealRaw.add_valid p.valid (RealRaw.ofRat_valid 1))

end ComputableAnalysis.BinomialPower
