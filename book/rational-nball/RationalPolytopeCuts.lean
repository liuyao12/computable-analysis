import RationalDissectionTransform

/-! Exact rational hyperplane clipping of finite convex hulls. -/
namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- Intersection of an edge with a rational cutting hyperplane. -/
def edgeIntersection {n : Nat} (a : Point n) (c : ℚ) (p q : Point n) : Point n :=
  fun i => ((c-dot a q)*p i+(dot a p-c)*q i)/(dot a p-dot a q)

/-- Retained vertices together with all crossing-edge intersections. All
vertices, including the new intersections, have rational coordinates. -/
noncomputable def clipVertices {n : Nat} (P : Polytope n) (a : Point n) (c : ℚ) : Polytope n := by
  classical
  exact P.filter (fun p => dot a p ≤ c) ∪
    ((P.product P).filter (fun pq => c < dot a pq.1 ∧ dot a pq.2 ≤ c)).image
      (fun pq => edgeIntersection a c pq.1 pq.2)

private theorem sum_div' {ι : Type} (s : Finset ι) (f : ι → ℚ) (a : ℚ) :
    (∑ i ∈ s, f i/a)=(∑ i ∈ s,f i)/a := by
  simp only [div_eq_mul_inv,Finset.sum_mul]

private theorem clip_pair_sum {H L : Type} [Fintype H] [Fintype L]
    (u e : H → ℚ) (v d : L → ℚ) (D : ℚ) :
    (∑ h : H, ∑ l : L, u h*v l*(e h+d l)/D) =
      ((∑ h,u h*e h)*(∑ l,v l)+(∑ h,u h)*(∑ l,v l*d l))/D := by
  simp_rw [mul_add,add_div]
  simp_rw [Finset.sum_add_distrib,sum_div']
  simp_rw [show ∀ h l, u h*v l*e h=(u h*e h)*v l by intros; ring,
    show ∀ h l, u h*v l*d l=u h*(v l*d l) by intros; ring]
  simp [← Finset.mul_sum,← Finset.sum_mul]

private theorem clip_pair_moment {H L : Type} [Fintype H] [Fintype L]
    (u e p : H → ℚ) (v d q : L → ℚ) (D : ℚ) :
    (∑ h : H, ∑ l : L, u h*v l*(d l*p h+e h*q l)/D) =
      ((∑ h,u h*p h)*(∑ l,v l*d l)+(∑ h,u h*e h)*(∑ l,v l*q l))/D := by
  simp_rw [show ∀ h l, u h*v l*(d l*p h+e h*q l)/D =
    (u h*p h)*(v l*d l)/D+(u h*e h)*(v l*q l)/D by intros; ring]
  simp_rw [Finset.sum_add_distrib,sum_div']
  simp [← Finset.mul_sum,← Finset.sum_mul,add_div]

private theorem dot_combination {n : Nat} (a p q : Point n) (r s : ℚ) :
    dot a (fun i => r*p i+s*q i)=r*dot a p+s*dot a q := by
  simp [dot,mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]

 theorem edgeIntersection_on_plane {n : Nat} (a p q : Point n) (c : ℚ)
    (hp : c < dot a p) (hq : dot a q ≤ c) :
    dot a (edgeIntersection a c p q)=c := by
  have hn : dot a p-dot a q ≠ 0 := by linarith
  have he : edgeIntersection a c p q =
      fun i => ((c-dot a q)/(dot a p-dot a q))*p i+
        ((dot a p-c)/(dot a p-dot a q))*q i := by
    funext i; unfold edgeIntersection; ring
  rw [he,dot_combination]
  field_simp; ring

 theorem edgeIntersection_mem_segment {n : Nat} (a p q : Point n) (c : ℚ)
    (hp : c < dot a p) (hq : dot a q ≤ c) :
    edgeIntersection a c p q ∈ segment ℚ p q := by
  have hd : 0 < dot a p-dot a q := by linarith
  refine ⟨(c-dot a q)/(dot a p-dot a q), (dot a p-c)/(dot a p-dot a q),
    div_nonneg (by linarith) hd.le,div_nonneg (by linarith) hd.le,?_,?_⟩
  · field_simp; ring
  · funext i; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,edgeIntersection]; ring

 theorem clipVertices_subset_cut {n : Nat} (P : Polytope n) (a : Point n) (c : ℚ) :
    (clipVertices P a c : Set (Point n)) ⊆ body P ∩ {x | dot a x ≤ c} := by
  classical
  intro x hx
  simp only [clipVertices,Finset.mem_coe,Finset.mem_union,Finset.mem_filter,
    Finset.mem_image] at hx
  rcases hx with ⟨hP,hc⟩ | ⟨⟨p,q⟩,⟨hpq,⟨hpc,hqc⟩⟩,rfl⟩
  · exact ⟨subset_convexHull ℚ _ hP,hc⟩
  · have hp := (Finset.mem_product.mp hpq).1
    have hq := (Finset.mem_product.mp hpq).2
    exact ⟨segment_subset_convexHull (by exact hp) (by exact hq)
      (edgeIntersection_mem_segment a p q c hpc hqc),
      le_of_eq (edgeIntersection_on_plane a p q c hpc hqc)⟩

private theorem halfspace_convex {n : Nat} (a : Point n) (c : ℚ) :
    Convex ℚ {x : Point n | dot a x ≤ c} := by
  intro x hx y hy r s hr hs hrs
  change dot a x ≤ c at hx
  change dot a y ≤ c at hy
  change dot a (fun i => r*x i+s*y i) ≤ c
  rw [dot_combination]
  have h1 := mul_le_mul_of_nonneg_left hx hr
  have h2 := mul_le_mul_of_nonneg_left hy hs
  calc
    r*dot a x+s*dot a y ≤ r*c+s*c := add_le_add h1 h2
    _ = c := by rw [← add_mul,hrs,one_mul]

 theorem body_clip_subset {n : Nat} (P : Polytope n) (a : Point n) (c : ℚ) :
    body (clipVertices P a c) ⊆ body P ∩ {x | dot a x ≤ c} :=
  convexHull_min (clipVertices_subset_cut P a c)
    ((convex_convexHull ℚ _).inter (halfspace_convex a c))

private theorem dot_sum {n : Nat} {ι : Type} [Fintype ι]
    (a : Point n) (w : ι → ℚ) (z : ι → Point n) :
    dot a (∑ i,w i • z i) = ∑ i,w i*dot a (z i) := by
  simp only [dot,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.mul_sum,mul_left_comm]

/-- Exact clipping coverage, including empty and lower-dimensional cuts. -/
theorem body_clip_eq {n : Nat} (P : Polytope n) (a : Point n) (c : ℚ) :
    body (clipVertices P a c)=body P ∩ {x | dot a x ≤ c} := by
  classical
  apply Set.Subset.antisymm (body_clip_subset P a c)
  intro x hx
  obtain ⟨ι,inst,w,z,hw,hs,hz,hxsum⟩ := mem_convexHull_iff_exists_fintype.mp hx.1
  letI : Fintype ι := inst
  let high : ι → Prop := fun i => c < dot a (z i)
  let H := {i : ι // high i}
  let L := {i : ι // ¬high i}
  let u : H → ℚ := fun i => w i
  let v : L → ℚ := fun i => w i
  let p : H → Point n := fun i => z i
  let q : L → Point n := fun i => z i
  let e : H → ℚ := fun i => dot a (p i)-c
  let d : L → ℚ := fun i => c-dot a (q i)
  let E : ℚ := ∑ i,u i*e i
  let D : ℚ := ∑ i,v i*d i
  have splitSum (f : ι → ℚ) : (∑ i : H,f i)+(∑ i : L,f i)=∑ i,f i :=
    Fintype.sum_subtype_add_sum_subtype high f
  have hm : (∑ i,u i)+(∑ i,v i)=1 := by
    simpa [u,v] using (splitSum w).trans hs
  have hcoord (j : Fin n) : (∑ i,u i*p i j)+(∑ i,v i*q i j)=x j := by
    have hsx := congrFun hxsum j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hsx
    exact (splitSum (fun i => w i*z i j)).trans hsx
  have he (i : H) : 0 < e i := by exact sub_pos.mpr i.property
  have hd (i : L) : 0 ≤ d i := by exact sub_nonneg.mpr (le_of_not_gt i.property)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (he i).le)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hd i))
  have hED : E ≤ D := by
    have hsDot := congrArg (dot a) hxsum
    rw [dot_sum] at hsDot
    have hsplit := splitSum (fun i => w i*dot a (z i))
    have hmass := congrArg (fun t : ℚ => t*c) hm
    have hh : E-D=dot a x-c := by
      dsimp [E,D,e,d]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul]
      dsimp [u,v,p,q] at *
      linarith only [hsDot,hsplit,hmass]
    have hc : dot a x ≤ c := hx.2
    linarith only [hh,hc]
  have hqmem (i : L) : q i ∈ (clipVertices P a c : Set (Point n)) := by
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hz i,le_of_not_gt i.property⟩
  by_cases hD0 : D=0
  · have hE0 : E=0 := le_antisymm (by simpa [hD0] using hED) hE
    have hu0 (i : H) : u i=0 := by
      have ht : u i*e i ≤ E := Finset.single_le_sum
        (fun (j : H) _ => mul_nonneg (hw j) (he j).le) (Finset.mem_univ i)
      have hprod : u i*e i=0 := le_antisymm (by simpa [hE0] using ht)
        (mul_nonneg (hw i) (he i).le)
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (he i))
    have hvm : ∑ i,v i=1 := by simpa [hu0] using hm
    apply mem_convexHull_of_exists_fintype v q (fun i => hw i) hvm hqmem
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simpa [hu0] using hcoord j
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    let coeff : H × L → ℚ := fun ij => u ij.1*v ij.2*(e ij.1+d ij.2)/D
    let vertex : H × L → Point n := fun ij => edgeIntersection a c (p ij.1) (q ij.2)
    let weight : L ⊕ (H × L) → ℚ := Sum.elim (fun i => v i*(1-E/D)) coeff
    let point : L ⊕ (H × L) → Point n := Sum.elim q vertex
    apply mem_convexHull_of_exists_fintype weight point
    · intro i
      cases i with
      | inl i =>
        exact mul_nonneg (hw i) (sub_nonneg.mpr ((div_le_one hDp).mpr hED))
      | inr ij =>
        exact div_nonneg (mul_nonneg (mul_nonneg (hw ij.1) (hw ij.2))
          (add_nonneg (he ij.1).le (hd ij.2))) hD
    · simp only [weight,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        coeff,Fintype.sum_prod_type]
      rw [clip_pair_sum,← Finset.sum_mul]
      change (∑ i,v i)*(1-E/D)+(E*(∑ i,v i)+(∑ i,u i)*D)/D=1
      field_simp
      have hm' := congrArg (fun t : ℚ => D*t) hm
      nlinarith only [hm']
    · intro i
      cases i with
      | inl i => exact hqmem i
      | inr ij =>
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(p ij.1,q ij.2),Finset.mem_filter.mpr ⟨?_,?_,?_⟩,rfl⟩
        · exact Finset.mem_product.mpr ⟨hz ij.1,hz ij.2⟩
        · exact ij.1.property
        · exact le_of_not_gt ij.2.property
    · ext j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,weight,point,
        Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
      have hlocal (i : H) (k : L) : coeff (i,k)*vertex (i,k) j =
          u i*v k*(d k*p i j+e i*q k j)/D := by
        have hn : e i+d k ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (he i) (hd k))
        have hn' : dot a (p i)-dot a (q k) ≠ 0 := by
          dsimp [e,d] at hn
          convert hn using 1 <;> ring
        dsimp [coeff,vertex,edgeIntersection,e,d]
        field_simp [hD0,hn']
        ring
      simp_rw [hlocal]
      rw [clip_pair_moment]
      simp_rw [show ∀ i,v i*(1-E/D)*q i j=(v i*q i j)*(1-E/D) by intro; ring]
      rw [← Finset.sum_mul]
      change (∑ i,v i*q i j)*(1-E/D)+
        ((∑ i,u i*p i j)*D+E*(∑ i,v i*q i j))/D=x j
      calc
        _ = (∑ i,u i*p i j)+(∑ i,v i*q i j) := by field_simp; ring
        _ = x j := hcoord j

/-- Refining every piece of a finite dissection is itself an exact dissection.
Flat overlaps are inherited, including between two different parent pieces. -/
theorem dissection_refinement {n : Nat} {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : Polytope n) (pieces : ι → Polytope n) (parts : ι → κ → Polytope n)
    (hP : Dissection P pieces) (hparts : ∀ i, Dissection (pieces i) (parts i)) :
    Dissection P (fun j : ι × κ => parts j.1 j.2) := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (hP.1 x).mp hx
      obtain ⟨j,hj⟩ := ((hparts i).1 x).mp hi
      exact ⟨(i,j),hj⟩
    · rintro ⟨⟨i,j⟩,hj⟩
      exact (hP.1 x).mpr ⟨i,((hparts i).1 x).mpr ⟨j,hj⟩⟩
  · rintro ⟨i,j⟩ ⟨k,l⟩ hne
    by_cases hik : i=k
    · subst k
      exact (hparts i).2 j l (by intro h; subst l; exact hne rfl)
    · obtain ⟨a,c,ha,hac⟩ := hP.2 i k hik
      refine ⟨a,c,ha,?_⟩
      intro x hx
      exact hac x ⟨((hparts i).1 x).mpr ⟨j,hx.1⟩,
        ((hparts k).1 x).mpr ⟨l,hx.2⟩⟩

private theorem dot_negative {n : Nat} (a x : Point n) : dot (-a) x = -dot a x := by
  simp [dot,Finset.sum_neg_distrib]

/-- The two sides of an actual rational cut cover the original hull and
intersect only in the cutting hyperplane. -/
theorem clip_dissection {n : Nat} (P : Polytope n) (a : Point n) (c : ℚ)
    (ha : a ≠ 0) :
    Dissection P (fun b : Bool => if b then clipVertices P (-a) (-c) else clipVertices P a c) := by
  have hlow (x : Point n) : x ∈ body (clipVertices P a c) ↔ x ∈ body P ∧ dot a x ≤ c := by
    rw [body_clip_eq]; rfl
  have hhigh (x : Point n) : x ∈ body (clipVertices P (-a) (-c)) ↔ x ∈ body P ∧ c ≤ dot a x := by
    rw [body_clip_eq]
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,dot_negative,neg_le_neg_iff]
  constructor
  · intro x
    constructor
    · intro hx
      by_cases hc : dot a x ≤ c
      · exact ⟨false,(hlow x).mpr ⟨hx,hc⟩⟩
      · exact ⟨true,(hhigh x).mpr ⟨hx,le_of_lt (lt_of_not_ge hc)⟩⟩
    · rintro ⟨b,hb⟩
      cases b
      · exact ((hlow x).mp hb).1
      · exact ((hhigh x).mp hb).1
  · intro b d hbd
    refine ⟨a,c,ha,?_⟩
    intro x hx
    cases b <;> cases d
    · exact False.elim (hbd rfl)
    · exact le_antisymm ((hlow x).mp hx.1).2 ((hhigh x).mp hx.2).2
    · exact le_antisymm ((hlow x).mp hx.2).2 ((hhigh x).mp hx.1).2
    · exact False.elim (hbd rfl)

/-- Exact retained-volume plus cap-volume identity, derived from the volume
axioms and the constructed clipping dissection. -/
theorem volume_clip_add {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) (ha : a ≠ 0) :
    V.volume P = V.volume (clipVertices P a c)+V.volume (clipVertices P (-a) (-c)) := by
  have h := V.dissection P _ (clip_dissection P a c ha)
  simpa [Fintype.sum_bool,add_comm] using h

/-- Clipping twice by the same plane does not change the body or volume. -/
theorem volume_clip_idempotent {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) :
    V.volume (clipVertices (clipVertices P a c) a c)=V.volume (clipVertices P a c) := by
  apply V.extensional
  simp [body_clip_eq,Set.inter_assoc]

/-- Two rational cuts commute geometrically and therefore in volume. -/
theorem volume_clip_commute {n : Nat} (V : Axioms n) (P : Polytope n)
    (a b : Point n) (c d : ℚ) :
    V.volume (clipVertices (clipVertices P a c) b d)=
      V.volume (clipVertices (clipVertices P b d) a c) := by
  apply V.extensional
  simp only [body_clip_eq]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- Repeated binary cutting constructs a finite common dissection. -/
noncomputable def cutLeaves {n : Nat} (P : Polytope n) : List (Point n × ℚ) → List (Polytope n)
  | [] => [P]
  | (a,c)::rest => cutLeaves (clipVertices P a c) rest ++
      cutLeaves (clipVertices P (-a) (-c)) rest

/-- The sum of the rational leaf volumes is exactly the original volume;
no approximation or new volume axiom is used. -/
theorem cutLeaves_volume {n : Nat} (V : Axioms n) (cuts : List (Point n × ℚ))
    (hnormal : ∀ ac ∈ cuts,ac.1 ≠ 0) (P : Polytope n) :
    ((cutLeaves P cuts).map V.volume).sum=V.volume P := by
  induction cuts generalizing P with
  | nil => simp [cutLeaves]
  | cons ac rest ih =>
    have ha := hnormal ac (List.mem_cons_self ..)
    have hr : ∀ ac ∈ rest,ac.1 ≠ 0 := fun ac hac => hnormal ac (List.mem_cons_of_mem _ hac)
    obtain ⟨a,c⟩ := ac
    simp only [cutLeaves,List.map_append,List.sum_append]
    rw [ih hr,ih hr,← volume_clip_add V P a c ha]

/-- Coverage by the constructed finite leaves. -/
theorem cutLeaves_coverage {n : Nat} (cuts : List (Point n × ℚ)) (P : Polytope n)
    (x : Point n) : x ∈ body P ↔ ∃ Q ∈ cutLeaves P cuts,x ∈ body Q := by
  induction cuts generalizing P with
  | nil => simp [cutLeaves]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    simp only [cutLeaves,List.mem_append,or_and_right,exists_or]
    rw [← ih,← ih,body_clip_eq,body_clip_eq]
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,dot_negative,neg_le_neg_iff]
    constructor
    · intro hx
      rcases le_total (dot a x) c with hc | hc
      · exact Or.inl ⟨hx,hc⟩
      · exact Or.inr ⟨hx,hc⟩
    · exact fun h => h.elim And.left And.left

/-- Nonnegativity is a consequence of the derived simplex formula for every
geometrically verified positive triangulation; it is not a further axiom. -/
theorem triangulation_volume_nonneg {n : Nat} (V : Axioms n) (P : Polytope n)
    {ι : Type} [Fintype ι] (p : ι → RationalSimplex.Vertices n)
    (hd : Dissection P (fun j => vertexSimplex (p j)))
    (hp : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (p j)).det) : 0 ≤ V.volume P := by
  rw [triangulation_volume V P p hd hp]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (hp i) (Nat.cast_nonneg _))

/-- Removing an explicitly triangulated cap can only decrease volume. -/
theorem volume_clip_le_of_cap_triangulation {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) (ha : a ≠ 0)
    {ι : Type} [Fintype ι] (p : ι → RationalSimplex.Vertices n)
    (hd : Dissection (clipVertices P (-a) (-c)) (fun j => vertexSimplex (p j)))
    (hp : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (p j)).det) :
    V.volume (clipVertices P a c) ≤ V.volume P := by
  have hn := triangulation_volume_nonneg V _ p hd hp
  rw [volume_clip_add V P a c ha]
  exact le_add_of_nonneg_right hn

/-- The exact incremental cap-subtraction law for an actual rational clip. -/
theorem volume_clip_update {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) (ha : a ≠ 0) :
    V.volume (clipVertices P a c)=V.volume P-V.volume (clipVertices P (-a) (-c)) := by
  rw [volume_clip_add V P a c ha]
  ring

noncomputable def retainedAfterCuts {n : Nat} (P : Polytope n) :
    List (Point n × ℚ) → Polytope n
  | [] => P
  | (a,c)::rest => retainedAfterCuts (clipVertices P a c) rest

noncomputable def removedCaps {n : Nat} (P : Polytope n) :
    List (Point n × ℚ) → List (Polytope n)
  | [] => []
  | (a,c)::rest => clipVertices P (-a) (-c) :: removedCaps (clipVertices P a c) rest

/-- Sequential clipping updates the preceding volume by the sum of exactly
those caps removed at each step. It never recomputes the final body's volume
in the incremental expression. -/
theorem sequential_clip_volume {n : Nat} (V : Axioms n) (cuts : List (Point n × ℚ))
    (hnormal : ∀ ac ∈ cuts,ac.1 ≠ 0) (P : Polytope n) :
    V.volume (retainedAfterCuts P cuts)=
      V.volume P-((removedCaps P cuts).map V.volume).sum := by
  induction cuts generalizing P with
  | nil => simp [retainedAfterCuts,removedCaps]
  | cons ac rest ih =>
    have ha := hnormal ac (List.mem_cons_self ..)
    have hr : ∀ ac ∈ rest,ac.1 ≠ 0 := fun ac hac => hnormal ac (List.mem_cons_of_mem _ hac)
    obtain ⟨a,c⟩ := ac
    simp only [retainedAfterCuts,removedCaps,List.map_cons,List.sum_cons]
    rw [ih hr,volume_clip_update V P a c ha]
    ring

/-- Every new tangent of a rational sphere sample is a genuine nonzero
cutting normal, including the coordinate-axis samples. -/
theorem unit_tangent_nonzero {n : Nat} (a : Point n) (hunit : normSq a=1) : a ≠ 0 := by
  intro hz
  simp [hz,normSq] at hunit

/-- The actual outer-polytope update by a finite list of sampled tangents
has an exact cap-subtraction volume identity in every dimension. -/
theorem tangent_clip_volume {n : Nat} (V : Axioms n) (P : Polytope n)
    (samples : List (Point n)) (hunit : ∀ a ∈ samples,normSq a=1) :
    V.volume (retainedAfterCuts P (samples.map (fun a => (a,1))))=
      V.volume P-((removedCaps P (samples.map (fun a => (a,1)))).map V.volume).sum := by
  apply sequential_clip_volume
  intro ac hac
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hac
  exact unit_tangent_nonzero a (hunit a ha)


#print axioms edgeIntersection_on_plane
#print axioms edgeIntersection_mem_segment
#print axioms clipVertices_subset_cut
#print axioms body_clip_subset
#print axioms body_clip_eq
#print axioms dissection_refinement
#print axioms clip_dissection
#print axioms volume_clip_add
#print axioms volume_clip_idempotent
#print axioms volume_clip_commute
#print axioms cutLeaves_volume
#print axioms cutLeaves_coverage
#print axioms triangulation_volume_nonneg
#print axioms volume_clip_le_of_cap_triangulation
#print axioms volume_clip_update
#print axioms sequential_clip_volume
#print axioms unit_tangent_nonzero
#print axioms tangent_clip_volume
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.edgeIntersection_on_plane,
    `ComputableAnalysis.RationalPolytopeVolume.edgeIntersection_mem_segment,
    `ComputableAnalysis.RationalPolytopeVolume.clipVertices_subset_cut,
    `ComputableAnalysis.RationalPolytopeVolume.body_clip_subset,
    `ComputableAnalysis.RationalPolytopeVolume.body_clip_eq,
    `ComputableAnalysis.RationalPolytopeVolume.dissection_refinement,
    `ComputableAnalysis.RationalPolytopeVolume.clip_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_add,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_idempotent,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_commute,
    `ComputableAnalysis.RationalPolytopeVolume.cutLeaves_volume,
    `ComputableAnalysis.RationalPolytopeVolume.cutLeaves_coverage,
    `ComputableAnalysis.RationalPolytopeVolume.triangulation_volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_le_of_cap_triangulation,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_update,
    `ComputableAnalysis.RationalPolytopeVolume.sequential_clip_volume,
    `ComputableAnalysis.RationalPolytopeVolume.unit_tangent_nonzero,
    `ComputableAnalysis.RationalPolytopeVolume.tangent_clip_volume]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked clipping/dissection endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
