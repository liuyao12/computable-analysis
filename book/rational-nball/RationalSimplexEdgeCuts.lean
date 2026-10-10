import RationalPolytopeCuts

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- The body of an ordered simplex has nonnegative volume, regardless of
which ordering is used to present it. The sign of the ordered simplex's
volume remains the determinant sign. No positivity axiom is added. -/
theorem vertexSimplex_volume_eq_abs (n : Nat) (V : Axioms n)
    (p : RationalSimplex.Vertices n) :
    V.volume (vertexSimplex p) = |(RationalSimplex.edgeMatrix p).det|/(n.factorial:ℚ) := by
  have h := simplexVolume_eq_coefficient n V p
  unfold simplexVolume RationalSimplex.determinantCoefficient at h
  by_cases hn : (RationalSimplex.edgeMatrix p).det < 0
  · rw [if_pos hn,abs_of_neg hn] at *
    rw [neg_div]
    linarith
  · rw [if_neg hn,abs_of_nonneg (le_of_not_gt hn)] at *
    exact h

theorem vertexSimplex_volume_nonneg (n : Nat) (V : Axioms n)
    (p : RationalSimplex.Vertices n) : 0 ≤ V.volume (vertexSimplex p) := by
  rw [vertexSimplex_volume_eq_abs]
  exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

/-- Every prescribed rational value at the vertices of a nonsingular
simplex is realized by a rational affine functional. -/
theorem simplex_affine_heights {n : Nat} (p : RationalSimplex.Vertices n)
    (hp : (RationalSimplex.edgeMatrix p).det ≠ 0) (r : Fin (n+1) → ℚ) :
    ∃ a : Point n, ∃ c : ℚ, ∀ i, dot a (p i)-c=r i := by
  let A := RationalSimplex.edgeMatrix p
  let s : Point n := fun j => r j.succ-r 0
  let a := A⁻¹.vecMul s
  let c := dot a (p 0)-r 0
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hp
  have ha : A.vecMul a=s := by
    dsimp [a]
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul A hunit,Matrix.vecMul_one]
  refine ⟨a,c,?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · dsimp [c]; ring
  · have he : (fun k => p j.succ k-p 0 k)=A.mulVec (axis j) := by
      ext k
      simp [A,RationalSimplex.edgeMatrix,Matrix.mulVec,dotProduct,axis]
    have hdot : dot a (fun k => p j.succ k-p 0 k)=r j.succ-r 0 := by
      rw [he]
      change dotProduct a (A.mulVec (axis j))=r j.succ-r 0
      rw [Matrix.dotProduct_mulVec,ha]
      simp [dotProduct,s,axis]
    have hsub : dot a (fun k => p j.succ k-p 0 k)=dot a (p j.succ)-dot a (p 0) := by
      simp [dot,mul_sub,Finset.sum_sub_distrib]
    rw [hsub] at hdot
    dsimp [c]
    linarith

/-- Rational interpolation on an edge; its coordinates can be computed
before any dissection is used. -/
def edgePoint {n : Nat} (p : RationalSimplex.Vertices n)
    (i j : Fin (n+1)) (t : ℚ) : Point n := fun k => t*p i k+(1-t)*p j k

def replaceVertex {n : Nat} (p : RationalSimplex.Vertices n)
    (i : Fin (n+1)) (q : Point n) : RationalSimplex.Vertices n :=
  fun k => if k=i then q else p k

private theorem dot_edgePoint {n : Nat} (a : Point n) (p : RationalSimplex.Vertices n)
    (i j : Fin (n+1)) (t : ℚ) :
    dot a (edgePoint p i j t)=t*dot a (p i)+(1-t)*dot a (p j) := by
  simp [dot,edgePoint,mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]

/-- A cut whose only strictly positive vertex is i and whose only strictly
negative vertex is j replaces vertex i by the edge intersection exactly. -/
theorem clip_simplex_one_crossing {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (c : ℚ) (i j : Fin (n+1)) (hij : i ≠ j) (t : ℚ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hheight : ∀ k, dot a (p k)-c=if k=i then 1-t else if k=j then -t else 0) :
    clipVertices (vertexSimplex p) a c = vertexSimplex (replaceVertex p i (edgePoint p i j t)) := by
  classical
  let q := edgePoint p i j t
  have hi : dot a (p i)=c+(1-t) := by have h := hheight i; simp at h; linarith
  have hj : dot a (p j)=c-t := by have h := hheight j; simp [Ne.symm hij] at h; linarith
  have hk (k : Fin (n+1)) (hki : k ≠ i) : dot a (p k) ≤ c := by
    have h := hheight k
    simp only [if_neg hki] at h
    split_ifs at h <;> linarith
  have hq : dot a q=c := by dsimp [q]; rw [dot_edgePoint,hi,hj]; ring
  have hedgej : edgeIntersection a c (p i) (p j)=q := by
    ext k
    simp only [edgeIntersection,hi,hj,q,edgePoint]
    ring
  have hedge (k : Fin (n+1)) (hki : k ≠ i) (hkj : k ≠ j) :
      edgeIntersection a c (p i) (p k)=p k := by
    have h := hheight k
    simp [hki,hkj] at h
    have hkc : dot a (p k)=c := by linarith
    ext l
    simp only [edgeIntersection,hi,hkc]
    field_simp [ne_of_gt (sub_pos.mpr ht1)]
    ring
  ext x
  constructor
  · intro hx
    simp only [clipVertices,Finset.mem_union,Finset.mem_filter,Finset.mem_image] at hx
    rcases hx with ⟨hp,hc⟩ | ⟨⟨y,z⟩,⟨hyz,hcross⟩,rfl⟩
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
      have hki : k ≠ i := by intro h; subst k; linarith
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ k,by simp [replaceVertex,hki]⟩
    · obtain ⟨hy,hz⟩ := Finset.mem_product.mp hyz
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hz
      have hki : k=i := by by_contra h; have hc := hk k h; linarith [hcross.1]
      subst k
      have hli : l ≠ i := by intro h; subst l; linarith [hcross.2]
      by_cases hlj : l=j
      · subst l
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,by simp [replaceVertex,hedgej,q]⟩
      · rw [hedge l hli hlj]
        exact Finset.mem_image.mpr ⟨l,Finset.mem_univ l,by simp [replaceVertex,hli]⟩
  · intro hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases hki : k=i
    · subst k
      simp only [replaceVertex,if_true]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(p i,p j),Finset.mem_filter.mpr ⟨?_,?_,?_⟩,hedgej⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,
          Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
      · linarith
      · linarith
    · simp only [replaceVertex,if_neg hki]
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k,Finset.mem_univ k,rfl⟩,hk k hki⟩


/-- Actual two-simplex edge dissection in every positive dimension. The
cutting hyperplane is constructed from the simplex's rational inverse matrix. -/
theorem simplex_edge_subdivision {n : Nat} (p : RationalSimplex.Vertices n)
    (hp : (RationalSimplex.edgeMatrix p).det ≠ 0)
    (i j : Fin (n+1)) (hij : i ≠ j) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1) :
    Dissection (vertexSimplex p) (fun b : Bool => if b then
      vertexSimplex (replaceVertex p j (edgePoint p i j t)) else
      vertexSimplex (replaceVertex p i (edgePoint p i j t))) := by
  let r : Fin (n+1) → ℚ := fun k => if k=i then 1-t else if k=j then -t else 0
  obtain ⟨a,c,hheight⟩ := simplex_affine_heights p hp r
  have hi := hheight i
  have hj := hheight j
  simp only [r,if_pos rfl,if_neg (Ne.symm hij)] at hi hj
  have ha : a ≠ 0 := by
    intro hz
    simp [hz,dot] at hi hj
    linarith
  have hlow := clip_simplex_one_crossing p a c i j hij t ht0 ht1 hheight
  have hneg : ∀ k, dot (-a) (p k)-(-c)=
      if k=j then 1-(1-t) else if k=i then -(1-t) else 0 := by
    intro k
    have hk := hheight k
    have hn : dot (-a) (p k) = -dot a (p k) := by simp [dot,Finset.sum_neg_distrib]
    rw [hn]
    by_cases hki : k=i
    · subst k; simp [r,hij] at hk ⊢; linarith
    · by_cases hkj : k=j
      · subst k; simp [r,hki] at hk ⊢; linarith
      · simp [r,hki,hkj] at hk ⊢; linarith
  have hhigh := clip_simplex_one_crossing p (-a) (-c) j i (Ne.symm hij)
    (1-t) (by linarith) (by linarith) hneg
  have hswap : edgePoint p j i (1-t)=edgePoint p i j t := by
    ext k; unfold edgePoint; ring
  rw [hswap] at hhigh
  have hd := clip_dissection (vertexSimplex p) a c ha
  simpa only [hlow,hhigh] using hd

/-- Clipping a verified dissection constructs a verified dissection of the
clipped body. Coverage and flat overlaps are proved, not assumed anew. -/
theorem dissection_clipped {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) (hd : Dissection P pieces)
    (a : Point n) (c : ℚ) :
    Dissection (clipVertices P a c) (fun i => clipVertices (pieces i) a c) := by
  constructor
  · intro x
    simp only [body_clip_eq,Set.mem_inter_iff,Set.mem_ofPred_eq]
    rw [hd.1 x]
    constructor
    · rintro ⟨⟨i,hi⟩,hc⟩; exact ⟨i,hi,hc⟩
    · rintro ⟨i,hi,hc⟩; exact ⟨⟨i,hi⟩,hc⟩
  · intro i j hij
    obtain ⟨b,d,hb,hbd⟩ := hd.2 i j hij
    refine ⟨b,d,hb,?_⟩
    intro x hx
    rw [body_clip_eq,body_clip_eq] at hx
    exact hbd x ⟨hx.1.1,hx.2.1⟩

/-- The same dissection survives a finite sequence of actual rational cuts. -/
theorem dissection_retained {n : Nat} {ι : Type} [Fintype ι]
    (cuts : List (Point n × ℚ)) (P : Polytope n) (pieces : ι → Polytope n)
    (hd : Dissection P pieces) :
    Dissection (retainedAfterCuts P cuts) (fun i => retainedAfterCuts (pieces i) cuts) := by
  induction cuts generalizing P pieces with
  | nil => exact hd
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    exact ih _ _ (dissection_clipped P pieces hd a c)


theorem retained_body_subset {n : Nat} (P : Polytope n)
    (cuts : List (Point n × ℚ)) : body (retainedAfterCuts P cuts) ⊆ body P := by
  induction cuts generalizing P with
  | nil => exact Set.Subset.refl _
  | cons ac rest ih =>
    exact (ih _).trans (fun x hx => (body_clip_subset P ac.1 ac.2 hx).1)

theorem retained_body_congr {n : Nat} (P Q : Polytope n)
    (h : body P=body Q) (cuts : List (Point n × ℚ)) :
    body (retainedAfterCuts P cuts)=body (retainedAfterCuts Q cuts) := by
  induction cuts generalizing P Q with
  | nil => exact h
  | cons ac rest ih =>
    apply ih
    simp only [body_clip_eq,h]

theorem volume_empty_body {n : Nat} (V : Axioms n) (P : Polytope n)
    (h : body P=∅) : V.volume P=0 := by
  have hd : Dissection P (fun i : Fin 0 => Fin.elim0 i) := by
    constructor
    · intro x; simp [h]
    · intro i; exact Fin.elim0 i
  simpa using V.dissection P _ hd

theorem flat_retained {n : Nat} (P : Polytope n)
    (h : Flat (body P)) (cuts : List (Point n × ℚ)) :
    Flat (body (retainedAfterCuts P cuts)) := by
  obtain ⟨a,c,ha,hac⟩ := h
  exact ⟨a,c,ha,fun x hx => hac x (retained_body_subset P cuts hx)⟩

private theorem vertexSimplex_flat {n : Nat} (p : RationalSimplex.Vertices n)
    (hp : (RationalSimplex.edgeMatrix p).det=0) : Flat (body (vertexSimplex p)) := by
  obtain ⟨a,c,ha,hac⟩ := transformed_simplex_flat (RationalSimplex.edgeMatrix p) hp
  rw [vertexSimplex_affine,body_translated]
  refine ⟨a,c+dot a (p 0),ha,?_⟩
  rintro x ⟨y,hy,rfl⟩
  simp only [dot,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  change dot a y+dot a (p 0)=c+dot a (p 0)
  rw [hac y hy]

private theorem simplex_halfspace_bound {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (c : ℚ) (h : ∀ i, dot a (p i) ≤ c) :
    ∀ x ∈ body (vertexSimplex p), dot a x ≤ c := by
  have hc : Convex ℚ {x : Point n | dot a x ≤ c} := by
    intro x hx y hy r s hr hs hrs
    change dot a (fun i => r*x i+s*y i) ≤ c
    simp only [dot,mul_add,Finset.sum_add_distrib,mul_left_comm,← Finset.mul_sum]
    change r*dot a x+s*dot a y ≤ c
    calc
      _ ≤ r*c+s*c := add_le_add (mul_le_mul_of_nonneg_left hx hr)
        (mul_le_mul_of_nonneg_left hy hs)
      _ = c := by rw [← add_mul,hrs,one_mul]
  apply convexHull_min _ hc
  rintro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  exact h i

private theorem simplex_clip_all_low {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (c : ℚ) (h : ∀ i, dot a (p i) ≤ c) :
    body (clipVertices (vertexSimplex p) a c)=body (vertexSimplex p) := by
  rw [body_clip_eq]
  exact Set.inter_eq_left.mpr (simplex_halfspace_bound p a c h)

private theorem simplex_clip_all_high_flat {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (ha : a ≠ 0) (c : ℚ) (h : ∀ i, c ≤ dot a (p i)) :
    Flat (body (clipVertices (vertexSimplex p) a c)) := by
  refine ⟨a,c,ha,?_⟩
  intro x hx
  rw [body_clip_eq] at hx
  have hn : ∀ i, dot (-a) (p i) ≤ -c := by
    intro i
    have hdot : dot (-a) (p i) = -dot a (p i) := by simp [dot,Finset.sum_neg_distrib]
    rw [hdot]; linarith [h i]
  have hh := simplex_halfspace_bound p (-a) (-c) hn x hx.1
  have hd : dot (-a) x = -dot a x := by simp [dot,Finset.sum_neg_distrib]
  rw [hd] at hh
  exact le_antisymm hx.2 (by linarith)

private def offPlaneCount {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (c : ℚ) : Nat :=
  (Finset.univ.filter (fun i => dot a (p i) ≠ c)).card

private theorem offPlaneCount_replace_lt {n : Nat} (p : RationalSimplex.Vertices n)
    (a : Point n) (c : ℚ) (i : Fin (n+1)) (q : Point n)
    (hi : dot a (p i) ≠ c) (hq : dot a q=c) :
    offPlaneCount (replaceVertex p i q) a c < offPlaneCount p a c := by
  unfold offPlaneCount
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    have h := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by intro he; subst k; simp [replaceVertex,hq] at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k,by simpa [replaceVertex,hki] using h⟩
  · intro he
    have hm : i ∈ Finset.univ.filter (fun k => dot a (p k) ≠ c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    rw [← he] at hm
    have hbad := (Finset.mem_filter.mp hm).2
    exact hbad (by simpa [replaceVertex] using hq)


/-- Every finite rational halfspace clipping of a simplex has nonnegative
volume. Edge subdivisions construct the positive pieces; no positivity or
monotonicity axiom and no supplied triangulation certificate is required. -/
theorem retained_simplex_volume_nonneg {n : Nat} (V : Axioms n)
    (p : RationalSimplex.Vertices n) (cuts : List (Point n × ℚ)) :
    0 ≤ V.volume (retainedAfterCuts (vertexSimplex p) cuts) := by
  classical
  induction cuts generalizing p with
  | nil => exact vertexSimplex_volume_nonneg n V p
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    have solve : ∀ m : Nat, ∀ p : RationalSimplex.Vertices n,
        offPlaneCount p a c ≤ m →
        0 ≤ V.volume (retainedAfterCuts (vertexSimplex p) ((a,c)::rest)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m rec =>
        intro p hm
        by_cases hp : (RationalSimplex.edgeMatrix p).det=0
        · rw [volume_flat n V _ (flat_retained _ (vertexSimplex_flat p hp) _)]
        by_cases ha : a=0
        · by_cases hc : 0 ≤ c
          · have hl : ∀ i, dot a (p i) ≤ c := by simp [ha,dot,hc]
            have he := retained_body_congr _ _ (simplex_clip_all_low p a c hl) rest
            rw [retainedAfterCuts,V.extensional _ _ he]
            exact ih p
          · have he : body (clipVertices (vertexSimplex p) a c)=∅ := by
              rw [body_clip_eq]; simp [ha,dot,hc]
            have hem : body (retainedAfterCuts (clipVertices (vertexSimplex p) a c) rest)=∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro x hx
              have hh := retained_body_subset _ rest hx
              rw [he] at hh
              exact hh
            rw [retainedAfterCuts,volume_empty_body V _ hem]
        by_cases hl : ∀ i, dot a (p i) ≤ c
        · have he := retained_body_congr _ _ (simplex_clip_all_low p a c hl) rest
          rw [retainedAfterCuts,V.extensional _ _ he]
          exact ih p
        by_cases hh : ∀ i, c ≤ dot a (p i)
        · rw [retainedAfterCuts,volume_flat n V _
            (flat_retained _ (simplex_clip_all_high_flat p a ha c hh) rest)]
        push Not at hl hh
        obtain ⟨i,hi⟩ := hl
        obtain ⟨j,hj⟩ := hh
        have hij : i ≠ j := by intro he; subst j; linarith
        let t : ℚ := (c-dot a (p j))/(dot a (p i)-dot a (p j))
        have hdpos : 0 < dot a (p i)-dot a (p j) := by linarith
        have ht0 : 0 < t := div_pos (by linarith) hdpos
        have ht1 : t < 1 := by
          apply (div_lt_one hdpos).mpr
          linarith
        let q := edgePoint p i j t
        have hq : dot a q=c := by
          dsimp [q]
          rw [dot_edgePoint]
          dsimp [t]
          field_simp
          ring
        let pi := replaceVertex p i q
        let pj := replaceVertex p j q
        have hri : offPlaneCount pi a c < offPlaneCount p a c :=
          offPlaneCount_replace_lt p a c i q (ne_of_gt hi) hq
        have hrj : offPlaneCount pj a c < offPlaneCount p a c :=
          offPlaneCount_replace_lt p a c j q (ne_of_lt hj) hq
        have hpi := rec _ (lt_of_lt_of_le hri hm) pi le_rfl
        have hpj := rec _ (lt_of_lt_of_le hrj hm) pj le_rfl
        have hsplit := simplex_edge_subdivision p hp i j hij t ht0 ht1
        have hd := dissection_retained ((a,c)::rest) _ _ hsplit
        have hv := V.dissection _ _ hd
        simp only [Fintype.sum_bool,if_true] at hv
        rw [hv]
        exact add_nonneg hpj hpi
    exact solve _ p le_rfl


/-- The axioms uniquely determine volume on every finitely clipped simplex. -/
theorem retained_simplex_volume_unique {n : Nat} (V W : Axioms n)
    (p : RationalSimplex.Vertices n) (cuts : List (Point n × ℚ)) :
    V.volume (retainedAfterCuts (vertexSimplex p) cuts) =
      W.volume (retainedAfterCuts (vertexSimplex p) cuts) := by
  classical
  induction cuts generalizing p with
  | nil => rw [retainedAfterCuts,vertexSimplex_volume_eq_abs,vertexSimplex_volume_eq_abs]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    have solve : ∀ m : Nat, ∀ p : RationalSimplex.Vertices n,
        offPlaneCount p a c ≤ m →
        V.volume (retainedAfterCuts (vertexSimplex p) ((a,c)::rest))=
        W.volume (retainedAfterCuts (vertexSimplex p) ((a,c)::rest)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m rec =>
        intro p hm
        by_cases hp : (RationalSimplex.edgeMatrix p).det=0
        · rw [volume_flat n V _ (flat_retained _ (vertexSimplex_flat p hp) _),
            volume_flat n W _ (flat_retained _ (vertexSimplex_flat p hp) _)]
        by_cases ha : a=0
        · by_cases hc : 0 ≤ c
          · have hl : ∀ i, dot a (p i) ≤ c := by simp [ha,dot,hc]
            have he := retained_body_congr _ _ (simplex_clip_all_low p a c hl) rest
            rw [retainedAfterCuts,V.extensional _ _ he,W.extensional _ _ he]
            exact ih p
          · have he : body (clipVertices (vertexSimplex p) a c)=∅ := by
              rw [body_clip_eq]; simp [ha,dot,hc]
            have hem : body (retainedAfterCuts (clipVertices (vertexSimplex p) a c) rest)=∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro x hx
              have hh := retained_body_subset _ rest hx
              rw [he] at hh
              exact hh
            rw [retainedAfterCuts,volume_empty_body V _ hem,volume_empty_body W _ hem]
        by_cases hl : ∀ i, dot a (p i) ≤ c
        · have he := retained_body_congr _ _ (simplex_clip_all_low p a c hl) rest
          rw [retainedAfterCuts,V.extensional _ _ he,W.extensional _ _ he]
          exact ih p
        by_cases hh : ∀ i, c ≤ dot a (p i)
        · rw [retainedAfterCuts,volume_flat n V _
            (flat_retained _ (simplex_clip_all_high_flat p a ha c hh) rest),
            volume_flat n W _ (flat_retained _ (simplex_clip_all_high_flat p a ha c hh) rest)]
        push Not at hl hh
        obtain ⟨i,hi⟩ := hl
        obtain ⟨j,hj⟩ := hh
        have hij : i ≠ j := by intro he; subst j; linarith
        let t : ℚ := (c-dot a (p j))/(dot a (p i)-dot a (p j))
        have hdpos : 0 < dot a (p i)-dot a (p j) := by linarith
        have ht0 : 0 < t := div_pos (by linarith) hdpos
        have ht1 : t < 1 := by
          apply (div_lt_one hdpos).mpr
          linarith
        let q := edgePoint p i j t
        have hq : dot a q=c := by
          dsimp [q]
          rw [dot_edgePoint]
          dsimp [t]
          field_simp
          ring
        let pi := replaceVertex p i q
        let pj := replaceVertex p j q
        have hri : offPlaneCount pi a c < offPlaneCount p a c :=
          offPlaneCount_replace_lt p a c i q (ne_of_gt hi) hq
        have hrj : offPlaneCount pj a c < offPlaneCount p a c :=
          offPlaneCount_replace_lt p a c j q (ne_of_lt hj) hq
        have hpi := rec _ (lt_of_lt_of_le hri hm) pi le_rfl
        have hpj := rec _ (lt_of_lt_of_le hrj hm) pj le_rfl
        have hsplit := simplex_edge_subdivision p hp i j hij t ht0 ht1
        have hd := dissection_retained ((a,c)::rest) _ _ hsplit
        have hv := V.dissection _ _ hd
        have hw := W.dissection _ _ hd
        simp only [Fintype.sum_bool,if_true] at hv hw
        rw [hv,hw]
        exact congrArg₂ (·+·) hpj hpi
    exact solve _ p le_rfl


/-- Any verified simplex dissection remains positive after arbitrary finite
cuts; its orientations need not be preselected. -/
theorem retained_triangulated_volume_nonneg {n : Nat} (V : Axioms n)
    (P : Polytope n) {ι : Type} [Fintype ι] (p : ι → RationalSimplex.Vertices n)
    (hd : Dissection P (fun i => vertexSimplex (p i)))
    (cuts : List (Point n × ℚ)) :
    0 ≤ V.volume (retainedAfterCuts P cuts) := by
  rw [V.dissection _ _ (dissection_retained cuts _ _ hd)]
  exact Finset.sum_nonneg (fun i _ => retained_simplex_volume_nonneg V (p i) cuts)

def matrixVertices {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    RationalSimplex.Vertices n := Fin.cases 0 (fun j i => A i j)

theorem vertexSimplex_matrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    vertexSimplex (matrixVertices A)=transformed (standardSimplex n) A := by
  classical
  rw [transformed_standardSimplex]
  ext x
  simp only [vertexSimplex,Finset.mem_image,Finset.mem_univ,true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨j.succ,rfl⟩

/-- Positivity of all bounded halfspace cuts of the unit cube, derived
from its explicit staircase dissection and the simplex formula. -/
theorem retained_cube_volume_nonneg (n : Nat) (V : Axioms n)
    (cuts : List (Point n × ℚ)) :
    0 ≤ V.volume (retainedAfterCuts (cube n 1) cuts) := by
  classical
  let p (σ : Equiv.Perm (Fin n)) := matrixVertices ((staircaseMatrix n).submatrix σ σ)
  have hd : Dissection (cube n 1) (fun σ => vertexSimplex (p σ)) := by
    have h := cube_staircase_dissection n
    simpa only [p,vertexSimplex_matrix,reindexed_staircase_eq_transformed] using h
  exact retained_triangulated_volume_nonneg V _ p hd cuts

/-- A cut cannot increase the volume of a clipped cube. Its removed cap
is itself a finite rational clipping with proved nonnegative volume. -/
theorem volume_clip_le_on_retained_cube (n : Nat) (V : Axioms n)
    (cuts : List (Point n × ℚ)) (a : Point n) (c : ℚ) (ha : a ≠ 0) :
    V.volume (clipVertices (retainedAfterCuts (cube n 1) cuts) a c) ≤
      V.volume (retainedAfterCuts (cube n 1) cuts) := by
  let P := retainedAfterCuts (cube n 1) cuts
  have hnon := retained_cube_volume_nonneg n V ((-a,-c)::cuts)
  have he : body (clipVertices P (-a) (-c))=
      body (retainedAfterCuts (cube n 1) ((-a,-c)::cuts)) := by
    have commute : ∀ (P : Polytope n) (cs : List (Point n × ℚ)),
        body (clipVertices (retainedAfterCuts P cs) (-a) (-c))=
        body (retainedAfterCuts (clipVertices P (-a) (-c)) cs) := by
      intro P cs
      induction cs generalizing P with
      | nil => rfl
      | cons ac rest ih =>
        rw [retainedAfterCuts,ih]
        apply retained_body_congr
        simp only [body_clip_eq]
        ext x; simp [and_assoc,and_comm]
    exact commute _ cuts
  rw [← V.extensional _ _ he] at hnon
  have hsum := volume_clip_add V P a c ha
  linarith


/-- Translations transport exact dissection coverage and flat overlaps. -/
theorem dissection_translated {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) (hd : Dissection P pieces)
    (b : Point n) : Dissection (translated P b) (fun i => translated (pieces i) b) := by
  constructor
  · intro x
    simp only [body_translated,Set.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,hi⟩ := (hd.1 y).mp hy
      exact ⟨i,y,hi,rfl⟩
    · rintro ⟨i,y,hy,rfl⟩
      exact ⟨y,(hd.1 y).mpr ⟨i,hy⟩,rfl⟩
  · intro i j hij
    obtain ⟨a,c,ha,hac⟩ := hd.2 i j hij
    refine ⟨a,c+dot a b,ha,?_⟩
    intro x hx
    rw [body_translated,body_translated] at hx
    obtain ⟨y,hy,hxy⟩ := hx.1
    obtain ⟨z,hz,hxz⟩ := hx.2
    have he : y=z := add_right_cancel (hxy.trans hxz.symm)
    subst z
    rw [← hxy]
    simp only [dot,Pi.add_apply,mul_add,Finset.sum_add_distrib]
    change dot a y+dot a b=c+dot a b
    rw [hac y ⟨hy,hz⟩]

theorem translated_vertexSimplex {n : Nat} (p : RationalSimplex.Vertices n) (b : Point n) :
    translated (vertexSimplex p) b=vertexSimplex (RationalSimplex.translated p b) := by
  classical
  simp only [translated,vertexSimplex,Finset.image_image]
  rfl

noncomputable def affineCube (n : Nat) (b : Point n) (r : ℚ) : Polytope n :=
  translated (transformed (cube n 1) (Matrix.diagonal (fun _ => r))) b

/-- Every finite clipping of a translated rational cube has nonnegative
volume; its simplex dissection is constructed explicitly. -/
theorem retained_affineCube_volume_nonneg (n : Nat) (V : Axioms n)
    (b : Point n) (r : ℚ) (hr : 0 < r) (cuts : List (Point n × ℚ)) :
    0 ≤ V.volume (retainedAfterCuts (affineCube n b r) cuts) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal (fun _ => r)
  have hA : A.det ≠ 0 := by
    simp [A,Matrix.det_diagonal,ne_of_gt hr]
  let p (σ : Equiv.Perm (Fin n)) := matrixVertices ((staircaseMatrix n).submatrix σ σ)
  have hd : Dissection (cube n 1) (fun σ => vertexSimplex (p σ)) := by
    have h := cube_staircase_dissection n
    simpa only [p,vertexSimplex_matrix,reindexed_staircase_eq_transformed] using h
  have ht := dissection_translated _ _ (dissection_transformed _ _ hd A hA) b
  simp only [transformed_vertexSimplex,translated_vertexSimplex] at ht
  exact retained_triangulated_volume_nonneg V _ _ ht cuts

end ComputableAnalysis.RationalPolytopeVolume


namespace ComputableAnalysis.RationalPolytopeVolume
#print axioms vertexSimplex_volume_eq_abs
#print axioms vertexSimplex_volume_nonneg
#print axioms simplex_affine_heights
#print axioms clip_simplex_one_crossing
#print axioms simplex_edge_subdivision
#print axioms dissection_clipped
#print axioms dissection_retained
#print axioms retained_body_subset
#print axioms retained_body_congr
#print axioms volume_empty_body
#print axioms flat_retained
#print axioms retained_simplex_volume_unique
#print axioms retained_simplex_volume_nonneg
#print axioms retained_triangulated_volume_nonneg
#print axioms vertexSimplex_matrix
#print axioms retained_cube_volume_nonneg
#print axioms volume_clip_le_on_retained_cube
#print axioms dissection_translated
#print axioms translated_vertexSimplex
#print axioms retained_affineCube_volume_nonneg
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.vertexSimplex_volume_eq_abs,
    `ComputableAnalysis.RationalPolytopeVolume.vertexSimplex_volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.simplex_affine_heights,
    `ComputableAnalysis.RationalPolytopeVolume.clip_simplex_one_crossing,
    `ComputableAnalysis.RationalPolytopeVolume.simplex_edge_subdivision,
    `ComputableAnalysis.RationalPolytopeVolume.dissection_clipped,
    `ComputableAnalysis.RationalPolytopeVolume.dissection_retained,
    `ComputableAnalysis.RationalPolytopeVolume.retained_body_subset,
    `ComputableAnalysis.RationalPolytopeVolume.retained_body_congr,
    `ComputableAnalysis.RationalPolytopeVolume.volume_empty_body,
    `ComputableAnalysis.RationalPolytopeVolume.flat_retained,
    `ComputableAnalysis.RationalPolytopeVolume.retained_simplex_volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.retained_simplex_volume_unique,
    `ComputableAnalysis.RationalPolytopeVolume.retained_triangulated_volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.vertexSimplex_matrix,
    `ComputableAnalysis.RationalPolytopeVolume.retained_cube_volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_le_on_retained_cube,
    `ComputableAnalysis.RationalPolytopeVolume.dissection_translated,
    `ComputableAnalysis.RationalPolytopeVolume.translated_vertexSimplex,
    `ComputableAnalysis.RationalPolytopeVolume.retained_affineCube_volume_nonneg]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
