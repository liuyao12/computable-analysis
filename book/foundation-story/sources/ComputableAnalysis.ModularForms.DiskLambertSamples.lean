import ComputableAnalysis.ModularForms.EisensteinUnitDisk

/-! Primary rational Lambert values on the full Euclidean unit disk. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor
set_option maxHeartbeats 1000000

theorem rational_norm_small (q : QComplex) (B : Rat) (h : q.normBound≤B) : Small (ofQComplex q) B := by
  apply (BoxApproximation.rational_small q).mono
  have hre := qabs_nonneg q.re
  have him := qabs_nonneg q.im
  dsimp [BoxApproximation.coordinateBound,QComplex.normBound] at *
  grind

theorem rational_difference_small (p q : QComplex) (B : Rat) (h : (QComplex.sub p q).normBound≤B) :
    Small (sub (ofQComplex p) (ofQComplex q)) B :=
  Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (equiv_symm (sub_constants p q)) (rational_norm_small _ _ h)

def atRadius (q : QComplex) (r : Rat) (k : Nat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ofQComplex (finitePrefix q k (cutoff r k+N)))
    (fun _ => ofQComplex_valid _) (tail r k)

theorem rational_cauchy (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r)
    (k m n : Nat) (hmn : m≤n) :
    Small (sub (ofQComplex (finitePrefix q k (cutoff r k+n))) (ofQComplex (finitePrefix q k (cutoff r k+m)))) (tail r k m) := by
  have h := prefix_tail q r hr hr1 hq k m (n-m)
  have he : cutoff r k+m+(n-m)=cutoff r k+n := by omega
  rw [he] at h
  exact rational_difference_small _ _ _ h

theorem atRadius_valid (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (k : Nat) :
    (atRadius q r k).Valid := RepresentedCauchySum.value_valid _ _ _ (tail_shrinks r hr hr1 k) (rational_cauchy q r hr hr1 hq k)

theorem atRadius_close (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (k N : Nat) :
    Small (sub (atRadius q r k) (ofQComplex (finitePrefix q k (cutoff r k+N)))) (tail r k N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (rational_cauchy q r hr hr1 hq k) N

/-- The radius is computed from the rational squared modulus. -/
def rationalRadius (q : QComplex) : Rat := (1+QComplex.normSq q)/2

theorem rationalRadius_pos (q : QComplex) : 0<rationalRadius q := by
  have := normSq_nonneg q; dsimp [rationalRadius]; grind only

theorem rationalRadius_lt_one (q : QComplex) (hq : QComplex.normSq q<1) : rationalRadius q<1 := by
  dsimp [rationalRadius]; grind only

theorem rationalRadius_inside (q : QComplex) : InDisk q (rationalRadius q) := by
  have := rat_square_nonneg_basic (1-QComplex.normSq q)
  dsimp [InDisk,rationalRadius]; grind only

theorem denominator_nonzero (q : QComplex) (hq : QComplex.normSq q<1) (n : Nat) :
    QComplex.normSq (RationalLambert.denominator q n)≠0 := by
  let r := rationalRadius q
  have hr := Rat.le_of_lt (rationalRadius_pos q)
  have hr1 := rationalRadius_lt_one q hq
  have hp := disk_power (rationalRadius_inside q) (n+1)
  have hpr := power_antitone hr (Rat.le_of_lt hr1) (show 1≤n+1 by omega)
  rw [Rat.pow_one] at hpr
  exact denominator_ne_zero hr hr1 (Rat.le_trans hp (EisensteinUnitDisk.square_mono _ _ (Rat.pow_nonneg hr) hpr))

def rationalValue (q : QComplex) (k : Nat) : ComplexRaw := atRadius q (rationalRadius q) k

theorem rationalValue_valid (q : QComplex) (hq : QComplex.normSq q<1) (k : Nat) : (rationalValue q k).Valid :=
  atRadius_valid q _ (Rat.le_of_lt (rationalRadius_pos q)) (rationalRadius_lt_one q hq) (rationalRadius_inside q) k

end ComputableAnalysis.ModularForms.DiskLambert
