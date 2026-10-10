import RationalSimplexGeometry

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

/-- Only the first coordinate is expanded, in positive dimension. -/
def firstStretch (n : Nat) (q : ℚ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.diagonal (fun i => if i=0 then q else 1)
noncomputable def stretchedSimplex (n : Nat) (q : ℚ) : Polytope (n+1) :=
  transformed (standardSimplex (n+1)) (firstStretch n q)

theorem firstStretch_det (n : Nat) (q : ℚ) : (firstStretch n q).det = q := by
  simp [firstStretch,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem firstStretch_mulVec_zero (n : Nat) (q : ℚ) (x : Point (n+1)) :
    (firstStretch n q).mulVec x 0 = q*x 0 := by
  simp [firstStretch,Matrix.mulVec_diagonal]
theorem firstStretch_mulVec_succ (n : Nat) (q : ℚ) (x : Point (n+1)) (i : Fin n) :
    (firstStretch n q).mulVec x i.succ = x i.succ := by
  simp [firstStretch,Matrix.mulVec_diagonal]

theorem mem_body_stretchedSimplex (n : Nat) (q : ℚ) (hq : 0 < q)
    (x : Point (n+1)) :
    x ∈ body (stretchedSimplex n q) ↔
      0 ≤ x 0 ∧ (∀ i : Fin n, 0 ≤ x i.succ) ∧ x 0/q+(∑ i : Fin n,x i.succ) ≤ 1 := by
  rw [stretchedSimplex,body_transformed]
  constructor
  · rintro ⟨y,hy,rfl⟩
    have h := (mem_body_standardSimplex _ y).mp hy
    rw [Fin.sum_univ_succ] at h
    simpa [firstStretch_mulVec_zero,firstStretch_mulVec_succ,ne_of_gt hq]
      using And.intro (mul_nonneg hq.le (h.1 0))
        (And.intro (fun i : Fin n => h.1 i.succ) h.2)
  · rintro ⟨hx0,hx,hbound⟩
    let y : Point (n+1) := Fin.cases (x 0/q) (fun i => x i.succ)
    refine ⟨y,?_,?_⟩
    · rw [mem_body_standardSimplex]
      constructor
      · intro i; refine Fin.cases ?_ ?_ i
        · exact div_nonneg hx0 hq.le
        · exact hx
      · simpa [y,Fin.sum_univ_succ] using hbound
    · ext i; refine Fin.cases ?_ ?_ i
      · simp only [firstStretch_mulVec_zero,y,Fin.cases_zero]
        field_simp [ne_of_gt hq]
      · intro j; simp [y,firstStretch_mulVec_succ]

/-- A rational elementary shear, retained as a determinant-one map under
our volume axioms. -/
def edgeShear (n : Nat) (a : ℚ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  fun i j => if i=0 then (if j=0 then 1 else -a) else (if i=j then 1 else 0)

theorem edgeShear_det (n : Nat) (a : ℚ) : (edgeShear n a).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [edgeShear]
  · intro i j hji
    change j < i at hji
    have hi : i ≠ 0 := by intro h; subst i; exact (not_lt_of_ge (Fin.zero_le j)) hji
    simp [edgeShear,hi,ne_of_gt hji]

theorem edgeShear_mulVec_zero (n : Nat) (a : ℚ) (x : Point (n+1)) :
    (edgeShear n a).mulVec x 0 = x 0-a*(∑ i : Fin n,x i.succ) := by
  simp [edgeShear,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,← Finset.mul_sum,sub_eq_add_neg]

theorem edgeShear_mulVec_succ (n : Nat) (a : ℚ) (x : Point (n+1)) (i : Fin n) :
    (edgeShear n a).mulVec x i.succ = x i.succ := by
  simp [edgeShear,Matrix.mulVec,dotProduct]

/-- The translated second simplex in an edge cut. -/
noncomputable def edgeCap (n : Nat) (a b : ℚ) : Polytope (n+1) :=
  translated (transformed (stretchedSimplex n b) (edgeShear n a)) (a • axis 0)

theorem body_translated {n : Nat} (P : Polytope n) (b : Point n) :
    body (translated P b) = (fun x => x+b) '' body P := by
  classical
  simp only [body,translated,Finset.coe_image]
  have h := (AffineEquiv.constVAdd ℚ (Point n) b).toAffineMap.image_convexHull
    (P : Set (Point n))
  change convexHull ℚ ((fun x : Point n => x+b) '' (P : Set (Point n))) =
    (fun x : Point n => x+b) '' convexHull ℚ (P : Set (Point n))
  have hc : (fun x : Point n => x+b) = (fun x => b+x) := funext (fun x => add_comm x b)
  rw [hc]
  simpa only [AffineEquiv.coe_toAffineMap,AffineEquiv.constVAdd_apply,vadd_eq_add] using h.symm



theorem mem_body_edgeCap (n : Nat) (a b : ℚ) (hb : 0 < b) (x : Point (n+1)) :
    x ∈ body (edgeCap n a b) ↔
      (∀ i : Fin n, 0 ≤ x i.succ) ∧
      a ≤ x 0+a*(∑ i : Fin n,x i.succ) ∧
      x 0+(a+b)*(∑ i : Fin n,x i.succ) ≤ a+b := by
  rw [edgeCap,body_translated,body_transformed]
  constructor
  · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
    have h := (mem_body_stretchedSimplex n b hb y).mp hy
    have hlast : y 0 ≤ (1-(∑ i : Fin n,y i.succ))*b :=
      (div_le_iff₀ hb).mp (by linarith [h.2.2])
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      edgeShear_mulVec_zero,edgeShear_mulVec_succ,axis,
      Fin.succ_ne_zero,if_false,if_true,mul_zero,mul_one,add_zero]
    refine ⟨h.2.1,?_,?_⟩ <;> nlinarith [h.1]
  · rintro ⟨hx,hlo,hhi⟩
    let y : Point (n+1) := Fin.cases (x 0+a*(∑ i : Fin n,x i.succ)-a)
      (fun i => x i.succ)
    refine ⟨(edgeShear n a).mulVec y,⟨y,?_,rfl⟩,?_⟩
    · rw [mem_body_stretchedSimplex n b hb]
      simp only [y,Fin.cases_zero,Fin.cases_succ]
      refine ⟨by linarith,hx,?_⟩
      have hm : (x 0+a*(∑ i : Fin n,x i.succ)-a)/b ≤ 1-(∑ i : Fin n,x i.succ) :=
        (div_le_iff₀ hb).mpr (by nlinarith)
      linarith
    · ext i; refine Fin.cases ?_ ?_ i
      · simp [y,edgeShear_mulVec_zero,axis]
        ring
      · intro j; simp [y,edgeShear_mulVec_succ,axis]

theorem edgeCap_volume (n : Nat) (V : Axioms (n+1)) (a b : ℚ) :
    V.volume (edgeCap n a b) = V.volume (stretchedSimplex n b) := by
  rw [edgeCap,V.translation,V.determinant_one _ _ (edgeShear_det n a)]

/-- The two simplexes in a rational edge cut cover exactly and meet only in
the rational hyperplane through the cut point and the remaining vertices. -/
theorem simplex_edge_dissection (n : Nat) (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    Dissection (stretchedSimplex n (a+b))
      (Fin.cases (stretchedSimplex n a) (fun _ : Fin 1 => edgeCap n a b)) := by
  have hab : 0 < a+b := add_pos ha hb
  have left_iff (x : Point (n+1)) :
      x ∈ body (stretchedSimplex n a) ↔
      0 ≤ x 0 ∧ (∀ i : Fin n,0 ≤ x i.succ) ∧ x 0+a*(∑ i : Fin n,x i.succ) ≤ a := by
    rw [mem_body_stretchedSimplex n a ha]
    constructor
    · rintro ⟨hx0,hx,h⟩
      refine ⟨hx0,hx,?_⟩
      have hm := (div_le_iff₀ ha).mp (show x 0/a ≤ 1-(∑ i : Fin n,x i.succ) by linarith)
      nlinarith
    · rintro ⟨hx0,hx,h⟩
      refine ⟨hx0,hx,?_⟩
      have hm : x 0/a ≤ 1-(∑ i : Fin n,x i.succ) :=
        (div_le_iff₀ ha).mpr (by nlinarith)
      linarith
  have parent_iff (x : Point (n+1)) :
      x ∈ body (stretchedSimplex n (a+b)) ↔
      0 ≤ x 0 ∧ (∀ i : Fin n,0 ≤ x i.succ) ∧
        x 0+(a+b)*(∑ i : Fin n,x i.succ) ≤ a+b := by
    rw [mem_body_stretchedSimplex n (a+b) hab]
    constructor
    · rintro ⟨hx0,hx,h⟩
      have hm := (div_le_iff₀ hab).mp (show x 0/(a+b) ≤ 1-(∑ i : Fin n,x i.succ) by linarith)
      exact ⟨hx0,hx,by nlinarith⟩
    · rintro ⟨hx0,hx,h⟩
      have hm : x 0/(a+b) ≤ 1-(∑ i : Fin n,x i.succ) :=
        (div_le_iff₀ hab).mpr (by nlinarith)
      exact ⟨hx0,hx,by linarith⟩
  have cover (x : Point (n+1)) :
      x ∈ body (stretchedSimplex n (a+b)) ↔
        x ∈ body (stretchedSimplex n a) ∨ x ∈ body (edgeCap n a b) := by
    rw [parent_iff,left_iff,mem_body_edgeCap n a b hb]
    constructor
    · rintro ⟨hx0,hx,hbound⟩
      by_cases hcut : x 0+a*(∑ i : Fin n,x i.succ) ≤ a
      · exact Or.inl ⟨hx0,hx,hcut⟩
      · exact Or.inr ⟨hx,le_of_lt (lt_of_not_ge hcut),hbound⟩
    · rintro (⟨hx0,hx,hcut⟩ | ⟨hx,hcut,hbound⟩)
      · have hs : (∑ i : Fin n,x i.succ) ≤ 1 := by nlinarith
        exact ⟨hx0,hx,by nlinarith⟩
      · have hs : (∑ i : Fin n,x i.succ) ≤ 1 := by nlinarith
        exact ⟨by nlinarith,hx,hbound⟩
  constructor
  · intro x
    constructor
    · intro h
      rcases (cover x).mp h with hl | hr
      · exact ⟨0,hl⟩
      · exact ⟨1,hr⟩
    · rintro ⟨j,hj⟩
      apply (cover x).mpr
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
  · intro j k hjk
    let normal : Point (n+1) := Fin.cases 1 (fun _ => a)
    have hn : normal ≠ 0 := by intro h; have he := congrFun h 0; simp [normal] at he
    refine ⟨normal,a,hn,?_⟩
    intro x hx
    have hlr : x ∈ body (stretchedSimplex n a) ∧ x ∈ body (edgeCap n a b) := by
      fin_cases j <;> fin_cases k <;> try exact False.elim (hjk rfl)
      · exact ⟨hx.1,hx.2⟩
      · exact ⟨hx.2,hx.1⟩
    have hl := (left_iff x).mp hlr.1
    have hr := (mem_body_edgeCap n a b hb x).mp hlr.2
    have he : x 0+a*(∑ i : Fin n,x i.succ) = a := le_antisymm hl.2.2 hr.2.1
    simpa [dot,normal,Fin.sum_univ_succ,← Finset.mul_sum] using he

/-- Rational edge dissection yields additivity of the stretched simplex's volume. -/
theorem stretchedSimplex_add (n : Nat) (V : Axioms (n+1)) (a b : ℚ)
    (ha : 0 < a) (hb : 0 < b) :
    V.volume (stretchedSimplex n (a+b)) =
      V.volume (stretchedSimplex n a)+V.volume (stretchedSimplex n b) := by
  have h := V.dissection _ _ (simplex_edge_dissection n a b ha hb)
  simpa [Fin.sum_univ_succ,edgeCap_volume] using h

theorem stretchedSimplex_zero (n : Nat) (V : Axioms (n+1)) :
    V.volume (stretchedSimplex n 0) = 0 := by
  apply volume_flat
  refine ⟨axis 0,0,?_,?_⟩
  · intro h; have he := congrFun h 0; simp [axis] at he
  · intro x hx
    rw [stretchedSimplex,body_transformed] at hx
    rcases hx with ⟨y,hy,rfl⟩
    simp [dot_axis,firstStretch_mulVec_zero]

theorem stretchedSimplex_one (n : Nat) (V : Axioms (n+1)) :
    V.volume (stretchedSimplex n 1) = V.volume (standardSimplex (n+1)) := by
  have hm : firstStretch n 1 = 1 := by ext i j; simp [firstStretch,Matrix.diagonal,Matrix.one_apply]
  have hp : stretchedSimplex n 1 = standardSimplex (n+1) := by
    classical
    have hid : Matrix.mulVec (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) = id :=
      funext Matrix.one_mulVec
    simp [stretchedSimplex,hm,transformed,hid]
  rw [hp]

theorem stretchedSimplex_nat_mul (n : Nat) (V : Axioms (n+1)) (q : ℚ)
    (hq : 0 < q) (m : Nat) :
    V.volume (stretchedSimplex n (m*q)) = m*V.volume (stretchedSimplex n q) := by
  induction m with
  | zero => simp [stretchedSimplex_zero]
  | succ m ih =>
    by_cases hz : m=0
    · subst m; simp
    · have hm : 0 < (m:ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,
        stretchedSimplex_add n V _ q (mul_pos hm hq) hq,ih]
      ring

theorem stretchedSimplex_ratio (n : Nat) (V : Axioms (n+1)) (a b : Nat)
    (hb : 0 < b) :
    V.volume (stretchedSimplex n ((a:ℚ)/b)) =
      ((a:ℚ)/b)*V.volume (standardSimplex (n+1)) := by
  have hbq : 0 < (b:ℚ) := by exact_mod_cast hb
  have hrec := stretchedSimplex_nat_mul n V (1/(b:ℚ)) (one_div_pos.mpr hbq) b
  have hb0 : (b:ℚ) ≠ 0 := ne_of_gt hbq
  have he : (b:ℚ)*(1/(b:ℚ))=1 := by field_simp
  rw [he,stretchedSimplex_one] at hrec
  have hm := stretchedSimplex_nat_mul n V (1/(b:ℚ)) (one_div_pos.mpr hbq) a
  have hae : (a:ℚ)*(1/(b:ℚ))=(a:ℚ)/b := by ring
  rw [hae] at hm
  rw [hm]
  rw [hrec]
  field_simp

theorem stretchedSimplex_volume (n : Nat) (V : Axioms (n+1)) (q : ℚ)
    (hq : 0 < q) :
    V.volume (stretchedSimplex n q) = q / (Nat.factorial (n+1):ℚ) := by
  have hn : 0 ≤ q.num := (Rat.num_pos.mpr hq).le
  have hrepr : ((q.num.toNat:Nat):ℚ)/(q.den:ℚ)=q := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hn,Rat.num_div_den]
  rw [← hrepr,stretchedSimplex_ratio n V _ _ q.pos,standardSimplex_volume]
  ring

#print axioms simplex_edge_dissection
#print axioms stretchedSimplex_volume
end ComputableAnalysis.RationalPolytopeVolume
