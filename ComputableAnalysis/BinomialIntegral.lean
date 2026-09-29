import ComputableAnalysis.GlobalBinomialIdentity

/-! Public binomial computations: internal exponent bounds and compact charts
are chosen by executable rational algorithms and hidden by proved agreement. -/
namespace ComputableAnalysis.BinomialPower.Global
open Integral

def exponentOrder (p : Real) : Nat := (BinomialPower.parameterBound p-1).num.natAbs+1

def chart (p : Real) (rho : Rat) (h0 : 0 ≤ rho) (h1 : rho < 1) : Chart :=
  ⟨exponentOrder p,rho,h0,h1⟩

theorem chart_bounds (p : Real) (rho : Rat) (h0 : 0 ≤ rho) (h1 : rho < 1) :
    (chart p rho h0 h1).BoundsParameter p := by
  intro s hs0 hs1
  have h := BinomialPower.parameterBound_spec p s hs0 hs1
  have hN := rational_upper_natural (BinomialPower.parameterBound p-1)
  change qabs (2-s) ≤ ((exponentOrder p : Nat) : Rat)
  unfold exponentOrder
  simp only [Rat.natCast_add]
  exact Rat.le_trans h hN

/-- The fallback branch is outside the mathematical domain. Public function
objects below restrict evaluation to `0 ≤ z < 1`. -/
def canonicalValue (p : Real) (z : Rat) : RealRaw :=
  if h : 0 ≤ z ∧ z < 1 then (chart p z h.1 h.2).value p z else RealRaw.ofRat 0

theorem canonicalValue_valid (p : Real) {z : Rat} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (canonicalValue p z).Valid := by
  rw [canonicalValue,dif_pos (And.intro hz0 hz1)]
  exact (chart p z hz0 hz1).value_valid (chart_bounds p z hz0 hz1) hz0 (Rat.le_refl)

theorem canonicalValue_agrees (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {z : Rat} (hz0 : 0 ≤ z) (hz : z ≤ A.radius) : (canonicalValue p z).Equiv (A.value p z) := by
  have hz1 : z < 1 := by have := A.belowOne; grind
  rw [canonicalValue,dif_pos (And.intro hz0 hz1)]
  exact (chart p z hz0 hz1).value_equiv A (chart_bounds p z hz0 hz1) hp (Real.equiv_refl p)
    hz0 (Rat.le_refl) hz

theorem canonicalValue_equiv {p q : Real} (heq : p.Equiv q) {z : Rat}
    (hz0 : 0 ≤ z) (hz1 : z < 1) : (canonicalValue p z).Equiv (canonicalValue q z) := by
  rw [canonicalValue,dif_pos (And.intro hz0 hz1),canonicalValue,dif_pos (And.intro hz0 hz1)]
  exact (chart p z hz0 hz1).value_equiv (chart q z hz0 hz1)
    (chart_bounds p z hz0 hz1) (chart_bounds q z hz0 hz1) heq hz0 (Rat.le_refl) (Rat.le_refl)

def canonicalIntegral (p : Real) (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) : RealRaw :=
  (chart p b (Rat.le_trans ha hab) hb).integral p a b

def canonicalFunction (p : Real) (a b : Rat) (ha : 0 ≤ a) (hb : b < 1) : FunctionOnInterval :=
  onInterval (canonicalValue p) a b (fun x hx => canonicalValue_valid p (Rat.le_trans ha hx.1) (by grind))

/-- Actual definite integral existence with no caller-supplied precision,
exponent bound, or chart. The exponent is any valid represented real. -/
theorem canonicalIntegral_hasIntegral (p : Real) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    HasIntegral (canonicalFunction p a b ha hb) (canonicalIntegral p a b ha hab hb) := by
  let A := chart p b (Rat.le_trans ha hab) hb
  have hp := chart_bounds p b (Rat.le_trans ha hab) hb
  have hv := A.integral_valid hp ha hab (Rat.le_refl)
  apply hasIntegral_of_uniform_approximation (g := fun _ x => A.value p x)
    (hg := fun _ x hx => A.value_valid hp (Rat.le_trans ha hx.1) hx.2)
    (J := fun _ => A.integral p a b) (e := fun _ => 0) hab hv
  · intro n; exact A.hasIntegral hp ha hab (Rat.le_refl)
  · intro eps; exact ⟨0,fun _ _ => Rat.le_of_lt eps.property⟩
  · intro n x hx i j
    have he := canonicalValue_agrees A hp (Rat.le_trans ha hx.1) hx.2
    have ho := (RealRaw.compareAt_overlap_iff _ _ i j).1
      (RealRaw.allStagesOverlap_of_equiv (canonicalValue_valid p (Rat.le_trans ha hx.1) (by have := A.belowOne; grind))
        (A.value_valid hp (Rat.le_trans ha hx.1) hx.2) he i j)
    change ((canonicalValue p x).compute i).lo ≤ ((A.value p x).compute j).hi ∧
      ((A.value p x).compute j).lo ≤ ((canonicalValue p x).compute i).hi at ho
    constructor <;> grind only
  · intro n i j
    have ho := (RealRaw.compareAt_overlap_iff _ _ i j).1 (RealRaw.allStagesOverlap_refl _ hv i j)
    change ((A.integral p a b).compute i).lo ≤ ((A.integral p a b).compute j).hi ∧
      ((A.integral p a b).compute j).lo ≤ ((A.integral p a b).compute i).hi at ho
    constructor <;> grind only

/-- Exact normalized endpoint identity, with all chart choices eliminated. -/
theorem canonicalIntegral_closedForm (p : Real) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (RealRaw.mul (RealRaw.sub p.preferred (RealRaw.ofRat 1)) (canonicalIntegral p a b ha hab hb)).Equiv
      (RealRaw.sub (canonicalValue (shiftParameter p) a) (canonicalValue (shiftParameter p) b)) := by
  let A := chart p b (Rat.le_trans ha hab) hb
  have hp := chart_bounds p b (Rat.le_trans ha hab) hb
  have hq := A.next_bounds hp
  have hav := A.next.value_valid hq ha (show a ≤ A.next.radius by exact hab)
  have hbv := A.next.value_valid hq (Rat.le_trans ha hab) (Rat.le_refl)
  have hac := canonicalValue_valid (shiftParameter p) ha (by grind)
  have hbc := canonicalValue_valid (shiftParameter p) (Rat.le_trans ha hab) hb
  have he := RealRaw.sub_equiv hav hac hbv hbc
    (RealRaw.equiv_symm (canonicalValue_agrees A.next hq ha (show a ≤ A.next.radius by exact hab)))
    (RealRaw.equiv_symm (canonicalValue_agrees A.next hq (Rat.le_trans ha hab) (Rat.le_refl)))
  exact RealRaw.equiv_trans
    (RealRaw.mul_valid (RealRaw.sub_valid p.valid (RealRaw.ofRat_valid 1))
      (A.integral_valid hp ha hab (Rat.le_refl)))
    (RealRaw.sub_valid hav hbv) (RealRaw.sub_valid hac hbc)
    (A.closedForm hp ha hab (Rat.le_refl)) he

theorem canonicalIntegral_equiv {p q : Real} (heq : p.Equiv q) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (canonicalIntegral p a b ha hab hb).Equiv (canonicalIntegral q a b ha hab hb) :=
  (chart p b (Rat.le_trans ha hab) hb).integral_equiv (chart q b (Rat.le_trans ha hab) hb)
    (chart_bounds p b (Rat.le_trans ha hab) hb) (chart_bounds q b (Rat.le_trans ha hab) hb)
    heq ha hab (Rat.le_refl) (Rat.le_refl)

end ComputableAnalysis.BinomialPower.Global
