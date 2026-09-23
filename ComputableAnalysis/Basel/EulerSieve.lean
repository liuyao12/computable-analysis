import ComputableAnalysis.Basel.ZetaEstimate

/-! Finite Euler sieving of reciprocal squares. The prime argument uses
these identities, rather than the existing Euclidean infinitude theorem. -/
namespace ComputableAnalysis.Basel.EulerSieve
open FormalPowerSeries DirichletSeries

def free : List Nat → Nat → Prop
  | [], _ => True
  | p::ps, k => ¬p∣k ∧ free ps k
instance freeDecidable : (ps : List Nat) → (k : Nat) → Decidable (free ps k)
  | [], _ => isTrue trivial
  | p::ps, k => @instDecidableAnd _ _ (inferInstance) (freeDecidable ps k)

def weight (k : Nat) : Rat := 1/((k:Rat)*(k:Rat))
def term (ps : List Nat) (k : Nat) : Rat := if free ps k then weight k else 0
def sieve (ps : List Nat) (n : Nat) : Rat := sumBelow (fun k=>term ps (k+1)) n
def coefficient : List Nat → Rat
  | [] => 1
  | p::ps => (1-weight p)*coefficient ps
def budget : List Nat → Nat
  | [] => 0
  | p::ps => (p+1)*budget ps+2*p

 theorem free_iff (ps : List Nat) (k : Nat) : free ps k ↔ ∀p, p∈ps → ¬p∣k := by
  induction ps with
  | nil => simp [free]
  | cons p ps ih => simp [free, ih]

 theorem free_mul {ps : List Nat} {p : Nat} (hp : BasicPrime p)
    (hps : ∀q, q∈ps → BasicPrime q) (hne : p∉ps) (k : Nat) :
    free ps (p*k) ↔ free ps k := by
  rw [free_iff, free_iff]
  constructor
  · intro h q hq hd; exact h q hq (Nat.dvd_trans hd (Nat.dvd_mul_left k p))
  · intro h q hq hd
    rcases basicPrime_dvd_of_dvd_mul (hps q hq) hd with hqp | hqk
    · have he := basicPrime_eq_of_dvd (hps q hq) hp hqp
      subst q; exact hne hq
    · exact h q hq hqk

 theorem weight_mul (p k : Nat) : weight (p*k)=weight p*weight k := by
  simp only [weight, Rat.natCast_mul, Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
  grind only

 theorem term_mul {ps : List Nat} {p : Nat} (hp : BasicPrime p)
    (hps : ∀q, q∈ps → BasicPrime q) (hne : p∉ps) (k : Nat) :
    term ps (p*k)=weight p*term ps k := by
  unfold term
  simp only [free_mul hp hps hne]
  split
  · exact weight_mul p k
  · grind only

 theorem sum_multiples (f : Nat→Rat) (p n : Nat) :
    sumBelow (fun k=>if p∣k+1 then f ((k+1)/p) else 0) n =
      sumBelow (fun k=>f (k+1)) (n/p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumBelow_succ, ih]
    by_cases hd : p∣n+1
    · rw [if_pos hd, Nat.succ_div_of_dvd hd, sumBelow_succ]
    · rw [if_neg hd, Nat.succ_div_of_not_dvd hd]; grind only

/-- Exact removal of the multiples of one new prime, at every finite cutoff. -/
 theorem sieve_cons {ps : List Nat} {p : Nat} (hp : BasicPrime p)
    (hps : ∀q, q∈ps → BasicPrime q) (hne : p∉ps) (n : Nat) :
    sieve (p::ps) n = sieve ps n-weight p*sieve ps (n/p) := by
  have ht (k : Nat) : term (p::ps) k =
      term ps k-(if p∣k then weight p*term ps (k/p) else 0) := by
    by_cases hd : p∣k
    · have hk : p*(k/p)=k := Nat.mul_div_cancel' hd
      have he := term_mul hp hps hne (k/p)
      rw [hk] at he
      simp only [term, free, hd, not_true_eq_false, false_and, ↓reduceIte]
      dsimp [term] at he; grind only
    · simp [term, free, hd]; split <;> grind only
  dsimp only [sieve]
  have hs : sumBelow (fun k=>term (p::ps) (k+1)) n =
      sumBelow (fun k=>term ps (k+1)-(if p∣k+1 then weight p*term ps ((k+1)/p) else 0)) n := by
    apply sumBelow_congr; intro k _; exact ht (k+1)
  rw [hs, sum_sub, sum_multiples (fun k=>weight p*term ps k) p n, sumBelow_mul]

 theorem sieve_nil (n : Nat) : sieve [] n=zetaTwoPartial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumBelow (fun k=>term [] (k+1)) (n+1)=_
    rw [sumBelow_succ]
    change sieve [] n+weight (n+1)=_
    rw [ih, zetaTwoPartial_succ]; rfl

 theorem sieve_all_primes {ps : List Nat} (hps : ∀q, q∈ps → BasicPrime q)
    (hall : ∀p, BasicPrime p → p∈ps) (n : Nat) (hn : 0<n) : sieve ps n=1 := by
  have ht (k : Nat) : term ps (k+1)=if k=0 then 1 else 0 := by
    by_cases hk : k=0
    · subst k
      have hf : free ps 1 := by
        rw [free_iff]; intro p hp hd
        have := Nat.dvd_one.mp hd; have := (hps p hp).1; omega
      simp [term, hf, weight, Rat.div_def]; grind only
    · have hf : ¬free ps (k+1) := by
        intro h
        obtain ⟨p,hp,hprime⟩ := exists_basicPrime_dvd (n:=k+1) (by omega)
        exact (free_iff ps (k+1)).mp h p (hall p hprime) hp
      simp [term, hf, hk]
  have he : sieve ps n=sumBelow (fun k=>if k=0 then (1:Rat) else 0) n := by
    apply sumBelow_congr; intro k _; exact ht k
  rw [he]
  cases n with
  | zero => omega
  | succ n =>
    rw [sum_shift]
    have hz : sumBelow (fun k=>if k+1=0 then (1:Rat) else 0) n=0 := by
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      rw [sum_const]; grind only
    rw [hz]; simp; grind only

end ComputableAnalysis.Basel.EulerSieve
