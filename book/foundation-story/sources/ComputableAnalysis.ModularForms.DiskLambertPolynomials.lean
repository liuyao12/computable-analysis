import ComputableAnalysis.ModularForms.DiskLambertLift
import ComputableAnalysis.RiemannHilbert.EntireMonomial
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums

/-! Finite polynomial certificates for the primary rational Lambert samples.
Both truncations are finite: the outer Lambert prefix and the inner geometric
kernel. They are used as proof approximations, not as a new value evaluator. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RationalLambert CauchyTaylor
set_option maxHeartbeats 1000000

def polynomialTerm (q : QComplex) (k n M : Nat) : QComplex :=
  QComplex.scaleRat (((n+1:Nat):Rat)^k)
    (QComplex.mul (QComplex.natPow q (n+1)) (geometric (QComplex.natPow q (n+1)) M))
def polynomialPrefix (q : QComplex) (k M : Nat) : Nat → QComplex
  | 0 => QComplex.zero
  | N+1 => QComplex.add (polynomialPrefix q k M N) (polynomialTerm q k N M)

def geometricScalar (q : Scalar) (n : Nat) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | M+1 => scalarSum oneScalar (scalarProduct (EntireMonomial.scalar q (n+1)) (geometricScalar q n M))
def geometricMap (n M : Nat) : DomainFunctions.Map where
  domain _ := True
  eval q _ := geometricScalar q n M
  domain_congr _ _ _ := Iff.rfl
  eval_congr q z _ _ he := by
    induction M with
    | zero => exact equiv_refl _ (ofQComplex_valid _)
    | succ M ih =>
      exact add_equiv (equiv_refl _ oneScalar.property)
        (mul_equiv (EntireMonomial.scalar q (n+1)).property (EntireMonomial.scalar z (n+1)).property
          (geometricScalar q n M).property (geometricScalar z n M).property
          (EntireMonomial.scalar_names q z he (n+1)) ih)
def geometricMap_holomorphic (n : Nat) : (M : Nat) → Holomorphic (geometricMap n M)
  | 0 => constantOn_holomorphic ScalarTopology.wholeData _
  | M+1 => ((constantOn_holomorphic ScalarTopology.wholeData oneScalar).sumOn
      ((EntireMonomial.holomorphic (n+1)).productOn (geometricMap_holomorphic n M) (fun _ _ => trivial))
      (fun _ _ => trivial)).transfer (geometricMap n (M+1)) (fun _ _ => trivial)
        ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩ (fun q _ => equiv_refl _ (geometricScalar q n (M+1)).property)
def polynomialTermMap (k n M : Nat) : DomainFunctions.Map :=
  productOn (constantOn (fun _ => True) ScalarTopology.wholeData.invariant
      (point ⟨((n+1:Nat):Rat)^k,0⟩))
    (productOn (EntireMonomial.function (n+1)) (geometricMap n M) (fun _ _ => trivial)) (fun _ _ => trivial)
def polynomialTermMap_holomorphic (k n M : Nat) : Holomorphic (polynomialTermMap k n M) :=
  (constantOn_holomorphic ScalarTopology.wholeData _).productOn
    ((EntireMonomial.holomorphic (n+1)).productOn (geometricMap_holomorphic n M) (fun _ _ => trivial)) (fun _ _ => trivial)
def polynomialScalar (q : Scalar) (k M : Nat) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | N+1 => scalarSum (polynomialScalar q k M N) ((polynomialTermMap k N M).eval q trivial)
def polynomialMap (k M N : Nat) : DomainFunctions.Map where
  domain _ := True
  eval q _ := polynomialScalar q k M N
  domain_congr _ _ _ := Iff.rfl
  eval_congr q z _ _ he := by
    induction N with
    | zero => exact equiv_refl _ (ofQComplex_valid _)
    | succ N ih => exact add_equiv ih ((polynomialTermMap k N M).eval_congr q z trivial trivial he)
def polynomialMap_holomorphic (k M : Nat) : (N : Nat) → Holomorphic (polynomialMap k M N)
  | 0 => constantOn_holomorphic ScalarTopology.wholeData _
  | N+1 => ((polynomialMap_holomorphic k M N).sumOn (polynomialTermMap_holomorphic k N M)
      (fun _ _ => trivial)).transfer (polynomialMap k M (N+1)) (fun _ _ => trivial)
        ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩ (fun q _ => equiv_refl _ (polynomialScalar q k M (N+1)).property)

theorem geometricMap_rational (q : QComplex) (n M : Nat) :
    ((geometricMap n M).eval (point q) trivial).val.Equiv (ofQComplex (geometric (QComplex.natPow q (n+1)) M)) := by
  induction M with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ M ih =>
    have hp := mul_equiv (EntireMonomial.scalar (point q) (n+1)).property (ofQComplex_valid (QComplex.natPow q (n+1)))
      (geometricScalar (point q) n M).property (ofQComplex_valid (geometric (QComplex.natPow q (n+1)) M))
      (power_constants q (n+1)) ih
    have hm := equiv_trans (mul_valid (EntireMonomial.scalar (point q) (n+1)).property (geometricScalar (point q) n M).property)
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) hp (RationalReciprocal.raw_mul_constants _ _)
    exact equiv_trans (geometricScalar (point q) n (M+1)).property
      (add_valid oneScalar.property (ofQComplex_valid _)) (ofQComplex_valid _) (add_equiv (equiv_refl _ oneScalar.property) hm) (add_constants _ _)

theorem polynomialTermMap_rational (q : QComplex) (k n M : Nat) :
    ((polynomialTermMap k n M).eval (point q) trivial).val.Equiv (ofQComplex (polynomialTerm q k n M)) := by
  have hp := mul_equiv (EntireMonomial.scalar (point q) (n+1)).property (ofQComplex_valid (QComplex.natPow q (n+1)))
    (geometricScalar (point q) n M).property (ofQComplex_valid (geometric (QComplex.natPow q (n+1)) M))
    (power_constants q (n+1)) (geometricMap_rational q n M)
  have hm := equiv_trans (mul_valid (EntireMonomial.scalar (point q) (n+1)).property (geometricScalar (point q) n M).property)
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) hp (RationalReciprocal.raw_mul_constants _ _)
  have h := mul_equiv (ofQComplex_valid (⟨((n+1:Nat):Rat)^k,0⟩ : QComplex)) (ofQComplex_valid _)
    (mul_valid (EntireMonomial.scalar (point q) (n+1)).property (geometricScalar (point q) n M).property)
    (ofQComplex_valid _) (equiv_refl _ (ofQComplex_valid _)) hm
  exact equiv_trans ((polynomialTermMap k n M).eval (point q) trivial).property
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) h (by
    have h := RationalReciprocal.raw_mul_constants (⟨((n+1:Nat):Rat)^k,0⟩ : QComplex)
      (QComplex.mul (QComplex.natPow q (n+1)) (geometric (QComplex.natPow q (n+1)) M))
    have he : QComplex.mul (⟨((n+1:Nat):Rat)^k,0⟩ : QComplex)
        (QComplex.mul (QComplex.natPow q (n+1)) (geometric (QComplex.natPow q (n+1)) M))=polynomialTerm q k n M := by
      simp only [polynomialTerm,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
      constructor <;> grind only
    exact he ▸ h)

theorem polynomialMap_rational (q : QComplex) (k M N : Nat) :
    ((polynomialMap k M N).eval (point q) trivial).val.Equiv (ofQComplex (polynomialPrefix q k M N)) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    exact equiv_trans (polynomialScalar (point q) k M (N+1)).property
      (add_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
      (add_equiv ih (polynomialTermMap_rational q k N M)) (add_constants _ _)

theorem power_disk_same (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (n : Nat) :
    InDisk (QComplex.natPow q (n+1)) r := by
  have hp := disk_power hq (n+1)
  have hm := power_antitone hr (Rat.le_of_lt hr1) (show 1≤n+1 by omega)
  simp only [Rat.pow_one] at hm
  exact Rat.le_trans hp (EisensteinUnitDisk.square_mono _ _ (Rat.pow_nonneg hr) hm)

theorem polynomialTerm_error (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1)
    (hq : InDisk q r) (k n M : Nat) :
    (QComplex.sub (term q k n) (polynomialTerm q k n M)).normBound≤majorant r k n*r^M := by
  have hd := kernel_remainder_disk hr hr1 (power_disk_same q r hr hr1 hq n) M
  have hm := disk_mul (disk_power hq (n+1)) hd
  have hc := disk_normBound _ _ (Rat.mul_nonneg (Rat.pow_nonneg hr)
    (Rat.mul_nonneg (Rat.pow_nonneg hr) (Rat.le_of_lt (Rat.inv_pos.mpr (by grind only : 0<1-r))))) hm
  have he : QComplex.sub (term q k n) (polynomialTerm q k n M)=
      QComplex.scaleRat (((n+1:Nat):Rat)^k) (QComplex.mul (QComplex.natPow q (n+1))
        (QComplex.sub (kernel (QComplex.natPow q (n+1))) (geometric (QComplex.natPow q (n+1)) M))) := by
    simp only [term,factor,polynomialTerm,kernel,denominator,RationalReciprocal.inverse,QComplex.inverse,
      QComplex.sub,QComplex.add,QComplex.neg,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  rw [he,QComplex.normBound_scaleRat]
  have hk : 0≤((n+1:Nat):Rat)^k := Rat.pow_nonneg (Rat.natCast_nonneg)
  have ha : qabs (((n+1:Nat):Rat)^k)=((n+1:Nat):Rat)^k := by unfold qabs; split <;> grind only
  rw [ha]
  have ht := Rat.mul_le_mul_of_nonneg_left hc hk
  dsimp [majorant] at *
  grind only

theorem polynomialPrefix_error (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1)
    (hq : InDisk q r) (k M N : Nat) :
    (QComplex.sub (finitePrefix q k N) (polynomialPrefix q k M N)).normBound≤majorantPrefix r k N*r^M := by
  induction N with
  | zero =>
    simp only [finitePrefix,polynomialPrefix,majorantPrefix,QComplex.sub,QComplex.add,QComplex.neg,QComplex.zero,QComplex.normBound,Rat.neg_zero,Rat.add_zero,Rat.zero_mul]
    decide +kernel
  | succ N ih =>
    have he : QComplex.sub (finitePrefix q k (N+1)) (polynomialPrefix q k M (N+1))=
        QComplex.add (QComplex.sub (finitePrefix q k N) (polynomialPrefix q k M N))
          (QComplex.sub (term q k N) (polynomialTerm q k N M)) := by
      simp only [finitePrefix,polynomialPrefix,QComplex.sub,QComplex.add,QComplex.neg,QComplex.mk.injEq]
      constructor <;> grind only
    rw [he]
    have hb := QComplex.normBound_add_le (QComplex.sub (finitePrefix q k N) (polynomialPrefix q k M N))
      (QComplex.sub (term q k N) (polynomialTerm q k N M))
    have ht := polynomialTerm_error q r hr hr1 hq k N M
    dsimp [majorantPrefix]
    grind only

/-- A finite bound uniform in both polynomial truncations. -/
def budget (r : Rat) (k : Nat) : Rat := majorantPrefix r k (cutoff r k)+tail r k 0
theorem budget_nonneg (r : Rat) (hr : 0≤r) (hr1 : r<1) (k : Nat) : 0≤budget r k :=
  Rat.add_nonneg (majorantPrefix_nonneg r hr hr1 k _) (tail_nonneg r hr hr1 k 0)
theorem prefix_norm (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (k N : Nat) :
    (finitePrefix q k N).normBound≤majorantPrefix r k N := by
  induction N with
  | zero =>
    simp only [finitePrefix,majorantPrefix,QComplex.zero,QComplex.normBound]
    decide +kernel
  | succ N ih =>
    exact Rat.le_trans (QComplex.normBound_add_le _ _) (rat_add_le_add ih (term_bound q r hr hr1 hq k N))
theorem norm_le_difference (a b : QComplex) : b.normBound≤a.normBound+(QComplex.sub a b).normBound := by
  have he : b=QComplex.sub a (QComplex.sub a b) := by
    cases b
    simp only [QComplex.sub,QComplex.add,QComplex.neg,QComplex.mk.injEq]
    constructor <;> grind only
  have h := QComplex.normBound_sub_le a (QComplex.sub a b)
  rw [←he] at h
  exact h
theorem polynomialPrefix_bound (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1)
    (hq : InDisk q r) (k M N : Nat) : (polynomialPrefix q k M N).normBound≤2*budget r k := by
  have hp := prefix_norm q r hr hr1 hq k N
  have he := polynomialPrefix_error q r hr hr1 hq k M N
  have hb := majorantPrefix_bound r hr hr1 k N
  have hm := CauchyTaylor.power_antitone hr (Rat.le_of_lt hr1) (show 0≤M by omega)
  rw [Rat.pow_zero] at hm
  have ht := Rat.mul_le_mul_of_nonneg_left hm (majorantPrefix_nonneg r hr hr1 k N)
  have hn := norm_le_difference (finitePrefix q k N) (polynomialPrefix q k M N)
  change majorantPrefix r k N≤budget r k at hb
  grind only

/-- The quantitative polynomial error on a compact disk. -/
def polynomialError (r : Rat) (k N : Nat) : Rat := tail r k N+budget r k*r^N
theorem polynomialError_nonneg (r : Rat) (hr : 0≤r) (hr1 : r<1) (k N : Nat) : 0≤polynomialError r k N :=
  Rat.add_nonneg (tail_nonneg r hr hr1 k N) (Rat.mul_nonneg (budget_nonneg r hr hr1 k) (Rat.pow_nonneg hr))
theorem geometric_shrinks (r : Rat) (hr : 0≤r) (hr1 : r<1) : ShrinksToZero (fun N => r^N) := by
  let C := (1-r)⁻¹
  have hC : 0≤C := Rat.le_of_lt (Rat.inv_pos.mpr (by grind only : 0<1-r))
  let B := C.ceil.natAbs+1
  have hCB : C≤(B:Rat) := by
    have hi : C.ceil≤(B:Int) := by dsimp [B]; have := Int.le_natAbs (a := C.ceil); omega
    exact Rat.le_trans Rat.le_ceil (by exact_mod_cast hi)
  apply shrinksToZero_of_natOverSuccBound (C := B)
  intro n
  have hp := power_nat_bound hr hr1 n
  have hx := Rat.mul_le_mul_of_nonneg_right hCB (Rat.le_of_lt (Rat.inv_pos.mpr
    (show (0:Rat)<((n+1:Nat):Rat) from Rat.natCast_pos.mpr (by omega))))
  dsimp [C] at hx
  rw [Rat.div_def] at hp ⊢
  exact Rat.le_trans hp hx
theorem polynomialError_shrinks (r : Rat) (hr : 0≤r) (hr1 : r<1) (k : Nat) : ShrinksToZero (polynomialError r k) :=
  RepresentedCauchySum.sum_shrinks _ _ (tail_shrinks r hr hr1 k)
    (SeriesLimitLaws.shrinks_scale _ (geometric_shrinks r hr hr1) (budget r k) (budget_nonneg r hr hr1 k))
theorem polynomialError_antitone (r : Rat) (hr : 0≤r) (hr1 : r<1) (k m n : Nat) (hmn : m≤n) :
    polynomialError r k n≤polynomialError r k m :=
  rat_add_le_add (tail_antitone r hr hr1 k m n hmn)
    (Rat.mul_le_mul_of_nonneg_left (CauchyTaylor.power_antitone hr (Rat.le_of_lt hr1) hmn) (budget_nonneg r hr hr1 k))
theorem rational_polynomial_close (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1)
    (hq : InDisk q r) (k N : Nat) :
    Small (sub (rationalValue q k) (ofQComplex (polynomialPrefix q k N (cutoff r k+N)))) (polynomialError r k N) := by
  have hq1 : QComplex.normSq q<1 := by
    have hh := Rat.mul_pos (show 0<1-r by grind only) (show 0<1+r by grind only)
    dsimp [InDisk] at hq; grind only
  have hc := atRadius_close q r hr hr1 hq k N
  have ha := Small.congr (sub_valid (atRadius_valid q r hr hr1 hq k) (ofQComplex_valid _))
    (sub_valid (rationalValue_valid q hq1 k) (ofQComplex_valid _))
    (FunctionTheory.sub_congr (equiv_symm (rational_atRadius q r hr hr1 hq k)) (equiv_refl _ (ofQComplex_valid _))) hc
  have he := polynomialPrefix_error q r hr hr1 hq k N (cutoff r k+N)
  have hb := Rat.mul_le_mul_of_nonneg_right (majorantPrefix_bound r hr hr1 k (cutoff r k+N)) (Rat.pow_nonneg hr (n := N))
  have hs := rational_difference_small _ _ _ (Rat.le_trans he hb)
  exact triangle _ _ _ (rationalValue_valid q hq1 k) (ofQComplex_valid _) (ofQComplex_valid _) _ _ ha hs

end ComputableAnalysis.ModularForms.DiskLambert
