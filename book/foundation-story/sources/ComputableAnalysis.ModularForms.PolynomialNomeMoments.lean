import ComputableAnalysis.ModularForms.WeightedNomePowers

/-! Constructed polynomial nome moments for the higher-weight Fourier rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def polynomialNomeMomentTerm (z : Scalar) (k n : Nat) : ComplexRaw :=
  scaleRat (((n+1:Nat):Rat)^k) (LocalODE.power z.val (n+1))

theorem polynomialNomeMomentTerm_valid (z : Scalar) (k n : Nat) :
    (polynomialNomeMomentTerm z k n).Valid := scaleRat_valid (LocalODE.power_valid _ z.property (n+1))

def polynomialNomeMomentRatio (r : Rat) (k : Nat) : Rat := 2*r*(2:Rat)^k

theorem polynomialNomeMomentRatio_nonneg (r : Rat) (k : Nat) (hr : 0≤r) :
    0≤polynomialNomeMomentRatio r k :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) (Rat.pow_nonneg (by decide))

theorem polynomialNomeMomentTerm_bound (z : Scalar) (r : Rat) (k : Nat)
    (hr : 0≤r) (hz : Small z.val r) (n : Nat) :
    Small (polynomialNomeMomentTerm z k n) (2*r*(polynomialNomeMomentRatio r k)^n) := by
  have h := LocalODE.small_scale (c := ((n+1:Nat):Rat)^k)
    (Rat.pow_nonneg Rat.natCast_nonneg) (LocalODE.power_small _ z.property r hr hz (n+1))
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right (lambertWeight_bound n k)
    (Rat.pow_nonneg (a := 2*r) (n := n+1) (Rat.mul_nonneg (by decide) hr))
  rw [Rat.pow_succ] at hm
  have hp : (polynomialNomeMomentRatio r k)^n=(2*r)^n*((2:Rat)^k)^n := by
    unfold polynomialNomeMomentRatio
    exact LocalODE.rational_mul_pow _ _ n
  rw [hp,Rat.pow_succ]
  grind only

def polynomialNomeMomentPrefix (z : Scalar) (k N : Nat) : ComplexRaw :=
  ScalarSeries.block (polynomialNomeMomentTerm z k) 0 N

theorem polynomialNomeMomentPrefix_valid (z : Scalar) (k N : Nat) :
    (polynomialNomeMomentPrefix z k N).Valid := ScalarSeries.block_valid _ (polynomialNomeMomentTerm_valid z k) 0 N

def polynomialNomeMomentSum (z : Scalar) (r : Rat) (k : Nat) : ComplexRaw :=
  ScalarSeries.value (polynomialNomeMomentTerm z k) (polynomialNomeMomentTerm_valid z k)
    r (polynomialNomeMomentRatio r k)

theorem polynomialNomeMomentSum_valid (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeMomentSum z r k).Valid :=
  ScalarSeries.value_valid _ _ r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hlocal
    (polynomialNomeMomentTerm_bound z r k hr hz)

theorem polynomialNomeMomentSum_close (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (polynomialNomeMomentSum z r k) (polynomialNomeMomentPrefix z k N))
      (4*r*(polynomialNomeMomentRatio r k)^N) :=
  ScalarSeries.value_close _ _ r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hlocal
    (polynomialNomeMomentTerm_bound z r k hr hz) N

theorem polynomialNomeMomentSum_congr (z w : Scalar) (r s : Rat) (k : Nat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : polynomialNomeMomentRatio r k≤(1:Rat)/2)
    (hslocal : polynomialNomeMomentRatio s k≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (he : z.val.Equiv w.val) :
    (polynomialNomeMomentSum z r k).Equiv (polynomialNomeMomentSum w s k) :=
  ScalarSeries.value_congr _ _ _ _ r _ s _ hr (polynomialNomeMomentRatio_nonneg r k hr)
    hs (polynomialNomeMomentRatio_nonneg s k hs) hrlocal hslocal
    (polynomialNomeMomentTerm_bound z r k hr hz) (polynomialNomeMomentTerm_bound w s k hs hw)
    (fun n => scaleRat_equiv (LocalODE.power_congr _ _ z.property w.property he (n+1)))

end ComputableAnalysis.ModularForms
