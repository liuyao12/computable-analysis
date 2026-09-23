import ComputableAnalysis.ZetaReal.Approximation

namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- An integer Lipschitz bound, computed by finite recursion. -/
def coefficientLip (m : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => coefficientLip m k*(k+m+4)+(m+3)^(m+1)

theorem coefficient_lipschitz {q m : Nat} {s t : Rat} (hs : InChart q m s) (ht : InChart q m t)
    (k : Nat) : qabs (coefficient s k-coefficient t k) ≤ (coefficientLip m k : Rat)*qabs (s-t) := by
  induction k with
  | zero => simp [coefficient, coefficientLip, qabs]; grind
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.natCast_nonneg (a := m)
    have hl := Rat.natCast_nonneg (a := coefficientLip m k)
    have hst := qabs_nonneg (s-t)
    have hfac : qabs ((k : Rat)+2-s) ≤ (k : Rat)+(m : Rat)+4 := by
      have h1 := chart_gt_one hs
      have h2 := hs.2
      apply qabs_le_of_neg_le_le <;> grind
    have hb := magnitude_bound ht k
    have he : ((k : Rat)+1)*(coefficient s (k+1)-coefficient t (k+1)) =
        (coefficient s k-coefficient t k)*((k : Rat)+2-s)+coefficient t k*(t-s) := by
      have h1 := coefficient_step s k
      have h2 := coefficient_step t k
      grind only
    have htri := qabs_add_le ((coefficient s k-coefficient t k)*((k : Rat)+2-s)) (coefficient t k*(t-s))
    have hneg : qabs (t-s)=qabs (s-t) := by
      rw [show t-s= -(s-t) by grind only, qabs_neg]
    have hprod := Rat.mul_le_mul_of_nonneg_left hfac (qabs_nonneg (coefficient s k-coefficient t k))
    have hprod2 := Rat.mul_le_mul_of_nonneg_right ih (by grind : 0 ≤ (k : Rat)+(m : Rat)+4)
    have hprod3 := Rat.mul_le_mul_of_nonneg_right hb hst
    have hn := qabs_nonneg (coefficient s (k+1)-coefficient t (k+1))
    have hdrop := Rat.mul_nonneg hk hn
    have heabs := congrArg qabs he
    rw [qabs_mul, qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1)] at heabs
    rw [qabs_mul, qabs_mul, hneg] at htri
    simp only [coefficientLip, Rat.natCast_add, Rat.natCast_mul, Rat.natCast_pow]
    change qabs (coefficient s (k+1)-coefficient t (k+1)) ≤
      ((coefficientLip m k : Rat)*((k : Rat)+(m : Rat)+4)+bound m)*qabs (s-t)
    change qabs (coefficient t k)*qabs (s-t) ≤ bound m*qabs (s-t) at hprod3
    grind only

def rectangleLip (m : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => rectangleLip m K+2*coefficientLip m K

theorem rectangle_lipschitz {q m : Nat} {s t : Rat} (hs : InChart q m s) (ht : InChart q m t)
    (K N : Nat) : qabs (rectangle s K N-rectangle t K N) ≤ (rectangleLip m K : Rat)*qabs (s-t) := by
  induction K with
  | zero => simp [rectangle, rectangleLip, qabs]; grind
  | succ K ih =>
    have h := coefficient_lipschitz hs ht K
    have hm := moment_nonneg K N
    have hb := moment_bound K N
    have hk := Rat.natCast_nonneg (a := K)
    have hx := Rat.mul_nonneg hk hm
    have hle : moment K N ≤ 2 := by grind only
    have h1 := Rat.mul_le_mul_of_nonneg_left hle (qabs_nonneg (coefficient s K-coefficient t K))
    have h2 := Rat.mul_le_mul_of_nonneg_left h (by decide : (0 : Rat) ≤ 2)
    have he : rectangle s (K+1) N-rectangle t (K+1) N =
        (rectangle s K N-rectangle t K N)+(coefficient s K-coefficient t K)*moment K N := by
      unfold rectangle; rw [sumBelow_succ, sumBelow_succ]; grind only
    have htri := qabs_add_le (rectangle s K N-rectangle t K N) ((coefficient s K-coefficient t K)*moment K N)
    rw [he]
    rw [qabs_mul, qabs_eq_self_of_nonneg hm] at htri
    simp only [rectangleLip, Rat.natCast_add, Rat.natCast_mul]
    grind only

def approximationLip (q m : Nat) (hq : 0 < q) (n : Nat) : Nat :=
  rectangleLip m (outerCutoff q m hq n)

theorem approx_lipschitz {q m : Nat} (hq : 0 < q) {s t : Rat}
    (hs : InChart q m s) (ht : InChart q m t) (n : Nat) :
    qabs (approx q m hq s n-approx q m hq t n) ≤
      (approximationLip q m hq n : Rat)*qabs (s-t) :=
  rectangle_lipschitz hs ht _ _

def function (q m : Nat) (hq : 0 < q) : FunctionOnInterval where
  raw := { definedAt := InChart q m
           compute := fun s _ => (raw q m hq s).compute
           rate := fun s _ => (raw q m hq s).rate }
  lower := lower q
  upper := (m : Rat)+2
  defined_on := fun _ hs => hs
  valid_on := fun _ hs => raw_valid hq hs

def imageBox (q m : Nat) (hq : 0 < q) (I : QInterval) (n : Nat) : QInterval :=
  let a := approx q m hq I.midpoint n
  let r := 4*(budget n).val+(approximationLip q m hq n : Rat)*I.width
  ⟨a-r,a+r⟩

def inputPrecision (q m : Nat) (hq : 0 < q) (n : Nat) : Nat :=
  (firstWitness (fun j => (2*approximationLip q m hq n : Nat)/((j+1 : Nat) : Rat) ≤ (budget n).val)
    (shrinksToZero_of_natOverSuccBound (C := 2*approximationLip q m hq n)
      (fun _ => Rat.le_refl) (budget n))).val+1

theorem inputPrecision_bound (q m : Nat) (hq : 0 < q) (n : Nat) :
    (2*approximationLip q m hq n : Nat)/(inputPrecision q m hq n : Rat) ≤ (budget n).val :=
  (firstWitness (fun j => (2*approximationLip q m hq n : Nat)/((j+1 : Nat) : Rat) ≤ (budget n).val)
    (shrinksToZero_of_natOverSuccBound (C := 2*approximationLip q m hq n)
      (fun _ => Rat.le_refl) (budget n))).property

theorem budget_unit (n : Nat) : 32*(budget n).val=1/((n+1 : Nat) : Rat) := by
  have hn : 0 < (n : Rat)+1 := by have := Rat.natCast_nonneg (a := n); grind
  have hi := Rat.mul_inv_cancel (32*((n : Rat)+1)) (by grind)
  have hj := Rat.mul_inv_cancel ((n : Rat)+1) (Rat.ne_of_gt hn)
  apply Rat.le_antisymm
  all_goals
    apply Rat.le_of_mul_le_mul_right (c := 32*((n : Rat)+1)) ?_ (by grind)
    simp only [budget, Rat.natCast_add, Rat.div_def, Rat.one_mul]
    have he : 32*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1))=32 := by
      calc
        _ = 32*((32*((n : Rat)+1))*(32*((n : Rat)+1))⁻¹) := by grind only
        _ = _ := by rw [hi]; grind
    have hf : ((n : Rat)+1)⁻¹*(32*((n : Rat)+1))=32 := by
      calc
        _ = 32*(((n : Rat)+1)*((n : Rat)+1)⁻¹) := by grind only
        _ = _ := by rw [hj]; grind
    change _ ≤ _
    first | (change 32*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1)) ≤ ((n : Rat)+1)⁻¹*(32*((n : Rat)+1)); rw [he,hf]; exact Rat.le_refl) | (change ((n : Rat)+1)⁻¹*(32*((n : Rat)+1)) ≤ 32*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1)); rw [he,hf]; exact Rat.le_refl)

theorem imageBox_width {q m : Nat} (hq : 0 < q) (I : QInterval)
    (hI : subintervalOf I (lower q) ((m : Rat)+2)) (n : Nat)
    (hw : I.width ≤ 1/(inputPrecision q m hq n : Rat)) :
    0 ≤ (imageBox q m hq I n).width ∧
      (imageBox q m hq I n).width ≤ 1/((n+1 : Nat) : Rat) := by
  have hi : 0 ≤ I.width := by have := hI.2.1; unfold QInterval.width; grind
  have hl := Rat.natCast_nonneg (a := approximationLip q m hq n)
  have hp := (budget n).property
  have hnon := Rat.mul_nonneg hl hi
  have hmul := Rat.mul_le_mul_of_nonneg_left hw (by grind : 0 ≤ 2*(approximationLip q m hq n : Rat))
  have hb := inputPrecision_bound q m hq n
  have hu := budget_unit n
  simp only [Rat.natCast_mul] at hb
  simp only [Rat.div_def] at hb hmul
  have he : (imageBox q m hq I n).width = 8*(budget n).val+2*(approximationLip q m hq n : Rat)*I.width := by
    unfold imageBox QInterval.width
    grind only
  rw [he]
  constructor <;> grind only

theorem imageBox_contains {q m : Nat} (hq : 0 < q) (I : QInterval)
    (hI : subintervalOf I (lower q) ((m : Rat)+2)) {s : Rat} (hs : InChart q m s)
    (n : Nat) (hlo : I.lo ≤ s) (hhi : s ≤ I.hi) :
    (imageBox q m hq I n).ContainsInterval ((raw q m hq s).compute n) := by
  have hm := QInterval.midpoint_mem hI.2.1
  have hc : InChart q m I.midpoint :=
    ⟨Rat.le_trans hI.1 hm.1, Rat.le_trans hm.2 hI.2.2⟩
  have hl := approx_lipschitz hq hs hc n
  have hd := QInterval.qabs_sub_midpoint_le_width hI.2.1 hlo hhi
  have hprod := Rat.mul_le_mul_of_nonneg_left hd (Rat.natCast_nonneg (a := approximationLip q m hq n))
  have ha := raw_enclosure q m hq s n
  have h1 := self_le_qabs (approx q m hq s n-approx q m hq I.midpoint n)
  have h2 := neg_qabs_le_self (approx q m hq s n-approx q m hq I.midpoint n)
  rcases ha with ⟨hal,har⟩
  constructor <;> dsimp [imageBox] <;> grind only

/-- A concrete interval-regular function, ready for the Chapter 1 real-input adapter. -/
def continuous (q m : Nat) (hq : 0 < q) : ContinuousFunctionOnInterval where
  function := function q m hq
  regular := {
    evalInterval := fun I _ n => imageBox q m hq I n
    inputPrecision := inputPrecision q m hq
    inputPrecision_pos := fun _ => Nat.zero_lt_succ _
    output_width := fun I hI n hw => imageBox_width hq I hI n hw
    contains_point_values := fun I hI _s hs n hlo hhi => imageBox_contains hq I hI hs n hlo hhi }

/-- Evaluation at an arbitrary represented real whose boxes lie in this chart. -/
def atReal (q m : Nat) (hq : 0 < q) (s : Real)
    (hs : ∀ n, subintervalOf (s.preferred.compute n) (lower q) ((m : Rat)+2)) : Real :=
  (continuous q m hq).applyReal s hs

end ComputableAnalysis.ZetaReal
