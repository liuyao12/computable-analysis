import RationalPolytopeCuts

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- A finite system of scalar rational inequalities has a rational solution
exactly when its zero rows and all lower/upper bound pairs are consistent. -/
theorem rational_scalar_feasible {ι : Type} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℚ)
    (hz : ∀ i ∈ s, a i=0 → 0 ≤ b i)
    (hp : ∀ i ∈ s, ∀ j ∈ s, a i<0 → 0<a j → a i*b j ≤ a j*b i) :
    ∃ z : ℚ, ∀ i ∈ s, a i*z ≤ b i := by
  classical
  let L := s.filter (fun i => a i<0)
  let U := s.filter (fun i => 0<a i)
  have pair : ∀ i ∈ L, ∀ j ∈ U, b i/a i ≤ b j/a j := by
    intro i hi j hj
    obtain ⟨his,hin⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs,hjp⟩ := Finset.mem_filter.mp hj
    rw [le_div_iff₀ hjp,div_mul_eq_mul_div,div_le_iff_of_neg hin]
    simpa [mul_comm] using hp i his j hjs hin hjp
  by_cases hL : L.Nonempty
  · obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image L (fun i => b i/a i) hL
    refine ⟨b i/a i,?_⟩
    intro j hjs
    by_cases hjn : a j<0
    · have hm := hmax j (Finset.mem_filter.mpr ⟨hjs,hjn⟩)
      have := (div_le_iff_of_neg hjn).mp hm
      simpa [mul_comm] using this
    · by_cases hjp : 0<a j
      · have hm := pair i hi j (Finset.mem_filter.mpr ⟨hjs,hjp⟩)
        have := (le_div_iff₀ hjp).mp hm
        simpa [mul_comm] using this
      · have hjz : a j=0 := by linarith
        simpa [hjz] using hz j hjs hjz
  · by_cases hU : U.Nonempty
    · obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image U (fun i => b i/a i) hU
      refine ⟨b i/a i,?_⟩
      intro j hjs
      have hjn : ¬ a j<0 := by
        intro h; exact hL ⟨j,Finset.mem_filter.mpr ⟨hjs,h⟩⟩
      by_cases hjp : 0<a j
      · have hm := hmin j (Finset.mem_filter.mpr ⟨hjs,hjp⟩)
        have := (le_div_iff₀ hjp).mp hm
        simpa [mul_comm] using this
      · have hjz : a j=0 := by linarith
        simpa [hjz] using hz j hjs hjz
    · refine ⟨0,?_⟩
      intro j hjs
      have hjn : ¬ a j<0 := by
        intro h; exact hL ⟨j,Finset.mem_filter.mpr ⟨hjs,h⟩⟩
      have hjp : ¬ 0<a j := by
        intro h; exact hU ⟨j,Finset.mem_filter.mpr ⟨hjs,h⟩⟩
      have hjz : a j=0 := by linarith
      simpa using hz j hjs hjz

/-- All coefficients, variables and bounds of the elimination procedure
are rational. There are m auxiliary coordinates and n retained coordinates. -/
structure RationalConstraint (n m : Nat) where
  weights : Fin m → ℚ
  normal : Point n
  bound : ℚ
  deriving DecidableEq

def RationalConstraint.holds {n m : Nat} (r : RationalConstraint n m)
    (w : Fin m → ℚ) (x : Point n) : Prop :=
  (∑ i,r.weights i*w i)+dot r.normal x ≤ r.bound

private def dropConstraint {n m : Nat} (r : RationalConstraint n (m+1)) :
    RationalConstraint n m := ⟨fun i => r.weights i.succ,r.normal,r.bound⟩

private def pairConstraint {n m : Nat} (r s : RationalConstraint n (m+1)) :
    RationalConstraint n m :=
  ⟨fun i => -r.weights 0*s.weights i.succ+s.weights 0*r.weights i.succ,
   fun i => -r.weights 0*s.normal i+s.weights 0*r.normal i,
   -r.weights 0*s.bound+s.weights 0*r.bound⟩

/-- Fourier–Motzkin elimination of one auxiliary rational coordinate. -/
def eliminateFirst {n m : Nat} (S : Finset (RationalConstraint n (m+1))) :
    Finset (RationalConstraint n m) :=
  (S.filter (fun r => r.weights 0=0)).image dropConstraint ∪
  ((S.product S).filter (fun rs => rs.1.weights 0<0 ∧ 0<rs.2.weights 0)).image
    (fun rs => pairConstraint rs.1 rs.2)

private theorem holds_cons {n m : Nat} (r : RationalConstraint n (m+1))
    (z : ℚ) (w : Fin m → ℚ) (x : Point n) :
    r.holds (Fin.cons z w) x ↔
    r.weights 0*z ≤ r.bound-(∑ i,r.weights i.succ*w i)-dot r.normal x := by
  unfold RationalConstraint.holds
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  constructor <;> intro h <;> linarith

private theorem holds_pair {n m : Nat} (r s : RationalConstraint n (m+1))
    (w : Fin m → ℚ) (x : Point n) :
    (pairConstraint r s).holds w x ↔
    r.weights 0*(s.bound-(∑ i,s.weights i.succ*w i)-dot s.normal x) ≤
    s.weights 0*(r.bound-(∑ i,r.weights i.succ*w i)-dot r.normal x) := by
  have hw : (∑ i,(-r.weights 0*s.weights i.succ+s.weights 0*r.weights i.succ)*w i)=
      -r.weights 0*(∑ i,s.weights i.succ*w i)+s.weights 0*(∑ i,r.weights i.succ*w i) := by
    simp_rw [show ∀ i,(-r.weights 0*s.weights i.succ+s.weights 0*r.weights i.succ)*w i=
      -r.weights 0*(s.weights i.succ*w i)+s.weights 0*(r.weights i.succ*w i) by intro; ring]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hx : dot (fun i => -r.weights 0*s.normal i+s.weights 0*r.normal i) x=
      -r.weights 0*dot s.normal x+s.weights 0*dot r.normal x := by
    unfold dot
    simp_rw [show ∀ i,(-r.weights 0*s.normal i+s.weights 0*r.normal i)*x i=
      -r.weights 0*(s.normal i*x i)+s.weights 0*(r.normal i*x i) by intro; ring]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  unfold RationalConstraint.holds pairConstraint
  rw [hw,hx]
  constructor <;> intro h <;> nlinarith

/-- Exact existential elimination, including empty systems and missing
upper or lower bounds. The witness produced by the proof is rational. -/
theorem eliminateFirst_iff {n m : Nat} (S : Finset (RationalConstraint n (m+1)))
    (w : Fin m → ℚ) (x : Point n) :
    (∀ r ∈ eliminateFirst S,r.holds w x) ↔
    ∃ z : ℚ, ∀ r ∈ S,r.holds (Fin.cons z w) x := by
  classical
  let a (r : RationalConstraint n (m+1)) := r.weights 0
  let b (r : RationalConstraint n (m+1)) :=
    r.bound-(∑ i,r.weights i.succ*w i)-dot r.normal x
  constructor
  · intro h
    have hz : ∀ r ∈ S,a r=0 → 0 ≤ b r := by
      intro r hr hra
      have hh := h (dropConstraint r) (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hra⟩,rfl⟩))
      change (∑ i,r.weights i.succ*w i)+dot r.normal x ≤ r.bound at hh
      dsimp [b]; linarith
    have hp : ∀ r ∈ S,∀ s ∈ S,a r<0 → 0<a s → a r*b s ≤ a s*b r := by
      intro r hr s hs hra hsa
      have hh := h (pairConstraint r s) (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(r,s),Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hr,hs⟩,hra,hsa⟩,rfl⟩))
      exact (holds_pair r s w x).mp hh
    obtain ⟨z,hz⟩ := rational_scalar_feasible S a b hz hp
    exact ⟨z,fun r hr => (holds_cons r z w x).mpr (hz r hr)⟩
  · rintro ⟨z,hz⟩ q hq
    simp only [eliminateFirst,Finset.mem_union,Finset.mem_image,Finset.mem_filter] at hq
    rcases hq with ⟨r,⟨hr,hra⟩,rfl⟩ | ⟨⟨r,s⟩,⟨hrs,hra,hsa⟩,rfl⟩
    · have hh := (holds_cons r z w x).mp (hz r hr)
      simp only [hra,zero_mul] at hh
      change (∑ i,r.weights i.succ*w i)+dot r.normal x ≤ r.bound
      linarith
    · obtain ⟨hr,hs⟩ := Finset.mem_product.mp hrs
      apply (holds_pair r s w x).mpr
      have h1 := (holds_cons r z w x).mp (hz r hr)
      have h2 := (holds_cons s z w x).mp (hz s hs)
      have h1' := mul_le_mul_of_nonneg_left h1 (le_of_lt hsa)
      have h2' := mul_le_mul_of_nonpos_left h2 (le_of_lt hra)
      nlinarith

end ComputableAnalysis.RationalPolytopeVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

/-- A literal finite elimination algorithm for all auxiliary coordinates. -/
def eliminateAll (n : Nat) : (m : Nat) →
    Finset (RationalConstraint n m) → Finset (RationalConstraint n 0)
  | 0,S => S
  | m+1,S => eliminateAll n m (eliminateFirst S)

theorem eliminateAll_iff (n m : Nat) (S : Finset (RationalConstraint n m))
    (x : Point n) :
    (∀ r ∈ eliminateAll n m S,r.holds (fun i => Fin.elim0 i) x) ↔
    ∃ w : Fin m → ℚ,∀ r ∈ S,r.holds w x := by
  induction m with
  | zero =>
    constructor
    · intro h; exact ⟨fun i => Fin.elim0 i,h⟩
    · rintro ⟨w,hw⟩ r hr
      have he : w=(fun i => Fin.elim0 i) := by ext i; exact Fin.elim0 i
      simpa [he] using hw r hr
  | succ m ih =>
    rw [eliminateAll,ih]
    constructor
    · rintro ⟨w,hw⟩
      obtain ⟨z,hz⟩ := (eliminateFirst_iff S w x).mp hw
      exact ⟨Fin.cons z w,hz⟩
    · rintro ⟨w,hw⟩
      refine ⟨fun i => w i.succ,(eliminateFirst_iff S _ x).mpr ⟨w 0,?_⟩⟩
      have he : Fin.cons (w 0) (fun i => w i.succ)=w := by
        ext i; refine Fin.cases rfl (fun j => rfl) i
      simpa only [he] using hw

/-- Rational projections of finite linear inequality systems have finite
rational halfspace presentations. No separation theorem over reals is used. -/
theorem rational_projection_halfspaces (n m : Nat)
    (S : Finset (RationalConstraint n m)) :
    ∃ cuts : Finset (Point n × ℚ),∀ x : Point n,
      (∃ w : Fin m → ℚ,∀ r ∈ S,r.holds w x) ↔
      ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2 := by
  classical
  let T := eliminateAll n m S
  refine ⟨T.image (fun r => (r.normal,r.bound)),?_⟩
  intro x
  rw [← eliminateAll_iff]
  constructor
  · intro h ac hac
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hac
    simpa [RationalConstraint.holds] using h r hr
  · intro h r hr
    have hh := h (r.normal,r.bound) (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
    simpa [RationalConstraint.holds] using hh

end ComputableAnalysis.RationalPolytopeVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

private theorem body_barycentric_indexed {n m : Nat} (P : Polytope n)
    (e : Fin m ≃ ↥P) (x : Point n) :
    x ∈ body P ↔ ∃ w : Fin m → ℚ,
      (∀ i,0 ≤ w i) ∧ (∑ i,w i)=1 ∧
      ∀ j,(∑ i,w i*(e i).val j)=x j := by
  classical
  have reindex (f : Point n → ℚ) : (∑ i,f (e i).val)=(∑ y ∈ P,f y) := by
    rw [e.sum_comp (fun y : ↥P => f y.val)]
    exact Finset.sum_attach P f
  rw [body,Finset.mem_convexHull']
  constructor
  · rintro ⟨v,hv,hs,hx⟩
    refine ⟨fun i => v (e i).val,fun i => hv _ (e i).property,?_,?_⟩
    · exact (reindex v).trans hs
    · intro j
      have hj := congrFun hx j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hj
      exact (reindex (fun y => v y*y j)).trans hj
  · rintro ⟨w,hw,hs,hx⟩
    let v : Point n → ℚ := fun y => if hy : y ∈ P then w (e.symm ⟨y,hy⟩) else 0
    have hv (i : Fin m) : v (e i).val=w i := by simp [v,(e i).property]
    refine ⟨v,?_,?_,?_⟩
    · intro y hy
      simpa [v,hy] using hw (e.symm ⟨y,hy⟩)
    · rw [← reindex v]
      simp_rw [hv]
      exact hs
    · ext j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      rw [← reindex (fun y => v y*y j)]
      simp_rw [hv]
      exact hx j

private def barycentricConstraints {n m : Nat} (p : Fin m → Point n) :
    Finset (RationalConstraint n m) :=
  (Finset.univ.image (fun i : Fin m =>
    (⟨fun k => if k=i then -1 else 0,0,0⟩ : RationalConstraint n m))) ∪
  {⟨fun _ => 1,0,1⟩,⟨fun _ => -1,0,-1⟩} ∪
  (Finset.univ.image (fun j : Fin n =>
    (⟨fun i => p i j,-axis j,0⟩ : RationalConstraint n m))) ∪
  (Finset.univ.image (fun j : Fin n =>
    (⟨fun i => -p i j,axis j,0⟩ : RationalConstraint n m)))

private theorem barycentricConstraints_iff {n m : Nat} (p : Fin m → Point n)
    (w : Fin m → ℚ) (x : Point n) :
    (∀ r ∈ barycentricConstraints p,r.holds w x) ↔
    (∀ i,0 ≤ w i) ∧ (∑ i,w i)=1 ∧ ∀ j,(∑ i,w i*p i j)=x j := by
  classical
  have hd (j : Fin n) : dot (-axis j) x = -x j := by
    simp [dot,axis,Finset.sum_neg_distrib]
  have hnon (i : Fin m) :
      (⟨fun k => if k=i then -1 else 0,0,0⟩ : RationalConstraint n m).holds w x ↔ 0 ≤ w i := by
    simp [RationalConstraint.holds,dot,ite_mul]
  have hslo : (⟨fun _ => 1,0,1⟩ : RationalConstraint n m).holds w x ↔ (∑ i,w i) ≤ 1 := by
    simp [RationalConstraint.holds,dot]
  have hshi : (⟨fun _ => -1,0,-1⟩ : RationalConstraint n m).holds w x ↔ 1 ≤ (∑ i,w i) := by
    simp [RationalConstraint.holds,dot,Finset.sum_neg_distrib]
  have hclo (j : Fin n) :
      (⟨fun i => p i j,-axis j,0⟩ : RationalConstraint n m).holds w x ↔
      (∑ i,w i*p i j) ≤ x j := by
    unfold RationalConstraint.holds
    rw [hd]
    simp only [mul_comm]
    constructor <;> intro h <;> linarith
  have hchi (j : Fin n) :
      (⟨fun i => -p i j,axis j,0⟩ : RationalConstraint n m).holds w x ↔
      x j ≤ (∑ i,w i*p i j) := by
    unfold RationalConstraint.holds
    rw [dot_axis]
    simp only [neg_mul,Finset.sum_neg_distrib]
    simp only [mul_comm]
    constructor <;> intro h <;> linarith
  simp only [barycentricConstraints,Finset.mem_union,Finset.mem_image,Finset.mem_univ,
    true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    refine ⟨fun i => (hnon i).mp (h _ (Or.inl (Or.inl (Or.inl ⟨i,rfl⟩)))),?_,?_⟩
    · exact le_antisymm ((hslo).mp (h _ (Or.inl (Or.inl (Or.inr (Or.inl rfl))))))
        ((hshi).mp (h _ (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))
    · intro j
      exact le_antisymm ((hclo j).mp (h _ (Or.inl (Or.inr ⟨j,rfl⟩))))
        ((hchi j).mp (h _ (Or.inr ⟨j,rfl⟩)))
  · rintro ⟨hw,hs,hx⟩ r hr
    rcases hr with ((hr | hr) | hr) | hr
    · obtain ⟨i,rfl⟩ := hr
      exact (hnon i).mpr (hw i)
    · rcases hr with rfl | rfl
      · exact hslo.mpr hs.le
      · exact hshi.mpr hs.ge
    · obtain ⟨j,rfl⟩ := hr
      exact (hclo j).mpr (hx j).le
    · obtain ⟨j,rfl⟩ := hr
      exact (hchi j).mpr (hx j).ge

/-- Every finite rational point hull has an exact finite rational halfspace
presentation. It is derived by eliminating its barycentric coordinates. -/
theorem pointHull_halfspaces {n : Nat} (P : Polytope n) :
    ∃ cuts : Finset (Point n × ℚ),∀ x : Point n,
      x ∈ body P ↔ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2 := by
  classical
  let m := Fintype.card ↥P
  let e : Fin m ≃ ↥P := (Fintype.equivFin ↥P).symm
  let p : Fin m → Point n := fun i => (e i).val
  obtain ⟨cuts,hcuts⟩ := rational_projection_halfspaces n m (barycentricConstraints p)
  refine ⟨cuts,?_⟩
  intro x
  rw [body_barycentric_indexed P e x,← hcuts x]
  exact exists_congr (fun w => (barycentricConstraints_iff p w x).symm)

end ComputableAnalysis.RationalPolytopeVolume

namespace ComputableAnalysis.RationalPolytopeVolume
#print axioms rational_scalar_feasible
#print axioms eliminateFirst_iff
#print axioms eliminateAll_iff
#print axioms rational_projection_halfspaces
#print axioms pointHull_halfspaces
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.rational_scalar_feasible,
    `ComputableAnalysis.RationalPolytopeVolume.eliminateFirst_iff,
    `ComputableAnalysis.RationalPolytopeVolume.eliminateAll_iff,
    `ComputableAnalysis.RationalPolytopeVolume.rational_projection_halfspaces,
    `ComputableAnalysis.RationalPolytopeVolume.pointHull_halfspaces]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
