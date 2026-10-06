import ComputableAnalysis.RiemannHilbert.LocalSystemMajorant

/-! Constructed finite-rank coefficient sums and exact initial vectors.
These are convergent vector series; their functional ODE and holomorphicity
are separate proof obligations. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory
variable {n : Nat}

def coordinateSeries (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (i : Fin n) (k : Nat) : ComplexRaw := (coefficient a initial k).val i

theorem coordinateSeries_valid (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (i : Fin n) (k : Nat) : (coordinateSeries a initial i k).Valid :=
  (coefficient a initial k).property i

def coordinateSum (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (C K R : Rat) (i : Fin n) : ComplexRaw :=
  LocalODE.coefficientSum (coordinateSeries a initial i) z.val
    (coordinateSeries_valid a initial i) z.property C K R

theorem coordinateSum_valid (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K) (hinit : CoordinateBound initial C)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (i : Fin n) :
    (coordinateSum a initial z C K R i).Valid :=
  LocalODE.coefficientSum_valid _ z.val (coordinateSeries_valid a initial i) z.property
    C K R hC hK hR (fun k => coefficient_majorant a initial M C K hM hC hK hMK haB hinit k i)
    hz hlocal

theorem coordinateSum_close (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K) (hinit : CoordinateBound initial C)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (i : Fin n) (N : Nat) :
    Small (sub (coordinateSum a initial z C K R i)
      (ScalarSeries.block (LocalODE.seriesTerm (coordinateSeries a initial i) z.val) 0 N))
      (4*C*(2*K*R)^N) :=
  LocalODE.coefficientSum_close _ z.val (coordinateSeries_valid a initial i) z.property
    C K R hC hK hR (fun k => coefficient_majorant a initial M C K hM hC hK hMK haB hinit k i)
    hz hlocal N

theorem coordinateSum_initial (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K) (hinit : CoordinateBound initial C)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (i : Fin n) :
    (coordinateSum a initial ⟨zero, ofQComplex_valid _⟩ C K R i).Equiv (initial.val i) := by
  simpa only [coordinateSum, coordinateSeries, coefficient_zero] using
    LocalODE.coefficientSum_zero _ (coordinateSeries_valid a initial i) C K R hC hK hR
      (fun k => coefficient_majorant a initial M C K hM hC hK hMK haB hinit k i) hlocal

/-- Both vector representations and independently certified bounds may change. -/
theorem coordinateSum_congr (a b : Nat → ValueMap (Fiber n) (Fiber n)) (x y : Fiber n)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x ≈ y) (z w : Scalar) (hzw : z.val.Equiv w.val)
    (M C K R P D L S : Rat)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L)
    (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (hx : CoordinateBound x C) (hy : CoordinateBound y D)
    (hz : Small z.val R) (hw : Small w.val S)
    (hq : 2*K*R ≤ (1 : Rat)/2) (hr : 2*L*S ≤ (1 : Rat)/2) (i : Fin n) :
    (coordinateSum a x z C K R i).Equiv (coordinateSum b y w D L S i) :=
  LocalODE.coefficientSum_congr_of_bounds _ _ z.val w.val
    (coordinateSeries_valid a x i) (coordinateSeries_valid b y i) z.property w.property
    (fun k => coefficient_congr a b x y hab hxy k i) hzw C K R D L S
    hC hK hR hD hL hS
    (fun k => coefficient_majorant a x M C K hM hC hK hMK haB hx k i)
    (fun k => coefficient_majorant b y P D L hP hD hL hPL hbB hy k i) hz hw hq hr

/-- An executable vector value on a guaranteed positive local domain. The
initial bound and convergence radius are selected inside this constructor. -/
def localValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z) : Fiber n :=
  ⟨fun i => coordinateSum a initial z (initialBound initial) K (LocalODE.solutionRadius K hK).val i,
    coordinateSum_valid a initial z M (initialBound initial) K (LocalODE.solutionRadius K hK).val
      hM (initialBound_nonneg initial) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
      hMK haB (initialBound_valid initial) (LocalODE.interior_bound _ z hz)
      (by have := LocalODE.solutionRadius_small K hK
          have := Rat.mul_nonneg hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
          grind)⟩

theorem localValue_initial (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) :
    localValue a initial M K hM hK hMK haB ⟨zero, ofQComplex_valid _⟩
      (LocalODE.interior_zero _ (LocalODE.solutionRadius K hK).property) ≈ initial := by
  intro i
  exact coordinateSum_initial a initial M (initialBound initial) K (LocalODE.solutionRadius K hK).val
    hM (initialBound_nonneg initial) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
    hMK haB (initialBound_valid initial)
    (by have := LocalODE.solutionRadius_small K hK
        have := Rat.mul_nonneg hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
        grind) i

theorem localValue_congr (a b : Nat → ValueMap (Fiber n) (Fiber n)) (x y : Fiber n)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x ≈ y)
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L)
    (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z)
    (hw : LocalODE.interior (LocalODE.solutionRadius L hL).val w) :
    localValue a x M K hM hK hMK haB z hz ≈ localValue b y P L hP hL hPL hbB w hw := by
  intro i
  exact coordinateSum_congr a b x y hab hxy z w hzw
    M (initialBound x) K (LocalODE.solutionRadius K hK).val
    P (initialBound y) L (LocalODE.solutionRadius L hL).val
    hM (initialBound_nonneg x) hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
    hP (initialBound_nonneg y) hL (Rat.le_of_lt (LocalODE.solutionRadius L hL).property)
    hMK hPL haB hbB (initialBound_valid x) (initialBound_valid y)
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw)
    (by have := LocalODE.solutionRadius_small K hK
        have := Rat.mul_nonneg hK (Rat.le_of_lt (LocalODE.solutionRadius K hK).property)
        grind)
    (by have := LocalODE.solutionRadius_small L hL
        have := Rat.mul_nonneg hL (Rat.le_of_lt (LocalODE.solutionRadius L hL).property)
        grind) i

end ComputableAnalysis.RiemannHilbert.LocalSystem
