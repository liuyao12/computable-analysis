import ComputableAnalysis.GlobalBinomialIntegral

/-! Exact identities on arbitrary positive compact charts. Both the exponent
name and the internal compact chart may be changed without changing values. -/
namespace ComputableAnalysis.BinomialPower.Global
open FormalPowerSeries ZetaReal RealParameterSample Integral FinitePolynomial

def Chart.next (A : Chart) : Chart := ⟨A.order+1,A.radius,A.nonneg,A.belowOne⟩

theorem Chart.next_bounds (A : Chart) {p : Real} (hp : A.BoundsParameter p) :
    A.next.BoundsParameter (shiftParameter p) := by
  intro t hlo hhi
  change (p.compute 0).lo+1 ≤ t at hlo
  change t ≤ (p.compute 0).hi+1 at hhi
  have h := hp (t-1) (by grind) (by grind)
  have ht := qabs_sub_le (2-(t-1)) 1
  rw [show (2 : Rat)-(t-1)-1=2-t by grind only,
    qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 1)] at ht
  change qabs (2-t) ≤ ((A.order+1 : Nat) : Rat)
  simp only [Rat.natCast_add]
  grind only

theorem integrated_prefix_eq (s x : Rat) (K : Nat) :
    integratedTaylorPrefix (coefficient s) K x=integratedPowerPolynomial s K x := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [integratedTaylorPrefix,integratedPowerPolynomial,sumBelow_succ] at *
    rw [ih]
    simp only [Rat.natCast_add,Rat.div_def]
    grind only

theorem finite_closedForm (s a b : Rat) (K : Nat) :
    (s-1)*(integratedTaylorPrefix (coefficient s) K b-integratedTaylorPrefix (coefficient s) K a) =
      powerPolynomial (s+1) (K+1) a-powerPolynomial (s+1) (K+1) b := by
  have h1 := integratedPowerPolynomial_identity s a K
  have h2 := integratedPowerPolynomial_identity s b K
  rw [integrated_prefix_eq,integrated_prefix_eq]
  grind only

/-- Exact compact integral identity for an arbitrary represented exponent.
The compact chart can approach base zero by any positive rational distance. -/
theorem Chart.closedForm (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius) :
    (RealRaw.mul (RealRaw.sub p.preferred (RealRaw.ofRat 1)) (A.integral p a b)).Equiv
      (RealRaw.sub (A.next.value (shiftParameter p) a) (A.next.value (shiftParameter p) b)) := by
  intro i
  let q := shiftParameter p
  let N := max i (max (A.observation p i) (A.next.observation q i))
  let K := max (A.cutoff i) (A.next.cutoff i)
  let s := (p.compute N).lo
  have observed (j : Nat) (hj : j ≤ N) : (p.compute j).lo ≤ s ∧ s ≤ (p.compute j).hi := by
    have h := p.valid.2.1 j N hj
    exact ⟨h.1,Rat.le_trans h.2.1 h.2.2⟩
  have ps := observed (A.observation p i) (by dsimp [N]; omega)
  have qs : (q.compute (A.next.observation q i)).lo ≤ s+1 ∧
      s+1 ≤ (q.compute (A.next.observation q i)).hi := by
    have h := observed (A.next.observation q i) (by dsimp [N]; omega)
    change (p.compute (A.next.observation q i)).lo+1 ≤ s+1 ∧
      s+1 ≤ (p.compute (A.next.observation q i)).hi+1
    constructor <;> grind only
  have hI := A.integral_contains hp ha hab hb (show A.cutoff i ≤ K by dsimp [K]; omega) ps
  have hA := A.next.value_contains (A.next_bounds hp) ha (show a ≤ A.next.radius by change a ≤ A.radius; grind)
    (show A.next.cutoff i ≤ K+1 by dsimp [K]; omega) qs
  have hB := A.next.value_contains (x := b) (A.next_bounds hp) (by grind) hb
    (show A.next.cutoff i ≤ K+1 by dsimp [K]; omega) qs
  have hparam : ((RealRaw.sub p.preferred (RealRaw.ofRat 1)).compute i).lo ≤ s-1 ∧
      s-1 ≤ ((RealRaw.sub p.preferred (RealRaw.ofRat 1)).compute i).hi := by
    have h := observed i (by dsimp [N]; omega)
    change (p.compute i).lo-1 ≤ s-1 ∧ s-1 ≤ (p.compute i).hi-1
    constructor <;> grind only
  have hleft := QBox.mulRealInterval_contains hparam.1 hparam.2 hI.1 hI.2
  rw [finite_closedForm] at hleft
  apply (RealRaw.compareAt_overlap_iff _ _ i i).2
  constructor
  · change _ ≤ ((A.next.value q a).compute i).hi-((A.next.value q b).compute i).lo
    exact Rat.le_trans hleft.1 (by grind only)
  · change ((A.next.value q a).compute i).lo-((A.next.value q b).compute i).hi ≤ _
    exact Rat.le_trans (by grind only) hleft.2

private theorem common_parameter {p q : Real} (heq : p.Equiv q) (i j : Nat) :
    ∃ s : Rat, ((p.compute i).lo ≤ s ∧ s ≤ (p.compute i).hi) ∧
      ((q.compute j).lo ≤ s ∧ s ≤ (q.compute j).hi) := by
  have ho := (RealRaw.compareAt_overlap_iff _ _ i j).1
    (RealRaw.allStagesOverlap_of_equiv p.valid q.valid heq i j)
  have po := RealRaw.interval_order_of_valid _ p.valid i
  have qo := RealRaw.interval_order_of_valid _ q.valid j
  change (p.compute i).lo ≤ (p.compute i).hi at po
  change (q.compute j).lo ≤ (q.compute j).hi at qo
  change (p.compute i).lo ≤ (q.compute j).hi ∧ (q.compute j).lo ≤ (p.compute i).hi at ho
  refine ⟨if (p.compute i).lo ≤ (q.compute j).lo then (q.compute j).lo else (p.compute i).lo, ?_⟩
  split <;> constructor <;> constructor <;> grind only

/-- Invariance under both exponent representation and compact chart choice. -/
theorem Chart.value_equiv (A B : Chart) {p q : Real}
    (hp : A.BoundsParameter p) (hq : B.BoundsParameter q) (heq : p.Equiv q)
    {x : Rat} (hx0 : 0 ≤ x) (hxA : x ≤ A.radius) (hxB : x ≤ B.radius) :
    (A.value p x).Equiv (B.value q x) := by
  intro n
  obtain ⟨s,hsA,hsB⟩ := common_parameter heq (A.observation p n) (B.observation q n)
  let K := max (A.cutoff n) (B.cutoff n)
  have hA := A.value_contains hp hx0 hxA (show A.cutoff n ≤ K by dsimp [K]; omega) hsA
  have hB := B.value_contains hq hx0 hxB (show B.cutoff n ≤ K by dsimp [K]; omega) hsB
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨Rat.le_trans hA.1 hB.2,Rat.le_trans hB.1 hA.2⟩

theorem Chart.integral_equiv (A B : Chart) {p q : Real}
    (hp : A.BoundsParameter p) (hq : B.BoundsParameter q) (heq : p.Equiv q)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hbA : b ≤ A.radius) (hbB : b ≤ B.radius) :
    (A.integral p a b).Equiv (B.integral q a b) := by
  intro n
  obtain ⟨s,hsA,hsB⟩ := common_parameter heq (A.observation p n) (B.observation q n)
  let K := max (A.cutoff n) (B.cutoff n)
  have hA := A.integral_contains hp ha hab hbA (show A.cutoff n ≤ K by dsimp [K]; omega) hsA
  have hB := B.integral_contains hq ha hab hbB (show B.cutoff n ≤ K by dsimp [K]; omega) hsB
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨Rat.le_trans hA.1 hB.2,Rat.le_trans hB.1 hA.2⟩

theorem Chart.supplied_closedForm (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A.radius) {I : RealRaw}
    (hI : HasIntegral (A.function p hp a b ha hb) I) :
    (RealRaw.mul (RealRaw.sub p.preferred (RealRaw.ofRat 1)) I).Equiv
      (RealRaw.sub (A.next.value (shiftParameter p) a) (A.next.value (shiftParameter p) b)) := by
  have hc := A.hasIntegral hp ha hab hb
  have hP := RealRaw.sub_valid p.valid (RealRaw.ofRat_valid 1)
  have he := RealRaw.mul_equiv hP hP hI.valid hc.valid (RealRaw.equiv_refl _ hP) (hI.unique hc)
  exact RealRaw.equiv_trans (RealRaw.mul_valid hP hI.valid) (RealRaw.mul_valid hP hc.valid)
    (RealRaw.sub_valid (A.next.value_valid (A.next_bounds hp) ha (by change a ≤ A.radius; grind))
      (A.next.value_valid (A.next_bounds hp) (by grind) hb)) he (A.closedForm hp ha hab hb)

end ComputableAnalysis.BinomialPower.Global
