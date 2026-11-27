import WatsonBinaryRank.Defs

/-!
# The code rule (Theorem 1)

`G` is a finite loopless multigraph, given by `ends : E → V × V` with distinct endpoints.
`incMat G` has rows `E` and columns `Option V` (`none` is the extra all-ones column):
the entry `(e, none)` is `1`, and `(e, some v)` is `1` iff `v` is an endpoint of `e`.

A family `fam Z ⊆ (ZMod 2)^k` (`Z ⊆ [k]`) has the *face property* if each `fam Z` meets every
face `{y' : y' = y outside Z}` in exactly one point. If all members of the family lie in a finite
set `S`, then the `k`-th Kronecker power of `incMat G` has an exact partition into
`|V|^k · |S|` all-ones rectangles.
-/

namespace WatsonBinaryRank

/-- A loopless multigraph: each edge has two distinct endpoints. -/
structure Graph (V E : Type) where
  ends : E → V × V
  ne : ∀ e, (ends e).1 ≠ (ends e).2

variable {V E : Type} [DecidableEq V]

/-- The edge–vertex incidence matrix with an extra all-ones column `none`. -/
def incMat (G : Graph V E) : BMat E (Option V)
  | _, none => true
  | e, some v => decide (v = (G.ends e).1 ∨ v = (G.ends e).2)

/-- `C` meets every face that fixes the coordinates outside `Z` in exactly one point. -/
def FaceProp {k : ℕ} (C : Set (Fin k → ZMod 2)) (Z : Finset (Fin k)) : Prop :=
  ∀ y : Fin k → ZMod 2, ∃! y', y' ∈ C ∧ ∀ i, i ∉ Z → y' i = y i

/-- The coordinates where a column index is the all-ones column. -/
def zeroSet {k : ℕ} (x : Fin k → Option V) : Finset (Fin k) :=
  Finset.univ.filter (fun i => x i = none)

/-- Labels: endpoint `.2` of an edge gets label `1`, everything else `0`. -/
def lab (G : Graph V E) {k : ℕ} (e : Fin k → E) (v : Fin k → V) : Fin k → ZMod 2 :=
  fun i => if v i = (G.ends (e i)).2 then 1 else 0

lemma zmod2_eq_zero_of_ne_one (a : ZMod 2) (h : a ≠ 1) : a = 0 := by
  revert a; decide

open Classical in
/-- **Theorem 1 (code rule).** -/
theorem code_rule [Fintype V] (G : Graph V E) (k : ℕ)
    (fam : Finset (Fin k) → Set (Fin k → ZMod 2)) (hfam : ∀ Z, FaceProp (fam Z) Z)
    (S : Finset (Set (Fin k → ZMod 2))) (hS : ∀ Z, fam Z ∈ S) :
    BrLE (kronPow (incMat G) k) (Fintype.card V ^ k * S.card) := by
  let ι := (Fin k → V) × S
  let rows : ι → Set (Fin k → E) := fun p =>
    {e | (∀ i, p.1 i = (G.ends (e i)).1 ∨ p.1 i = (G.ends (e i)).2) ∧ lab G e p.1 ∈ p.2.1}
  let cols : ι → Set (Fin k → Option V) := fun p =>
    {x | (∀ i, x i = none ∨ x i = some (p.1 i)) ∧ fam (zeroSet x) = p.2.1}
  refine ⟨ι, inferInstance, rows, cols, ?_, ?_, ?_⟩
  · simp [ι, Fintype.card_prod, Fintype.card_fun]
  · -- every rectangle is all-ones
    rintro ⟨v, s⟩ e ⟨he, -⟩ x ⟨hx, -⟩
    rw [kronPow_eq_true]
    intro i
    rcases hx i with h | h <;> rw [h]
    · rfl
    · simp only [incMat, decide_eq_true_eq]; exact he i
  · -- every one lies in exactly one rectangle
    intro e x hex
    rw [kronPow_eq_true] at hex
    have hend : ∀ i w, x i = some w → w = (G.ends (e i)).1 ∨ w = (G.ends (e i)).2 := by
      intro i w hw
      have := hex i
      rw [hw] at this
      simpa [incMat] using this
    set Z := zeroSet x with hZ
    -- the point outside `Z`
    let yo : Fin k → ZMod 2 := fun i =>
      match x i with
      | none => 0
      | some w => if w = (G.ends (e i)).2 then 1 else 0
    obtain ⟨y0, ⟨hy0C, hy0out⟩, hy0uniq⟩ := hfam Z yo
    let v : Fin k → V := fun i =>
      match x i with
      | some w => w
      | none => if y0 i = 1 then (G.ends (e i)).2 else (G.ends (e i)).1
    have hmemZ : ∀ i, i ∈ Z ↔ x i = none := by
      intro i; simp [hZ, zeroSet]
    -- `lab e v = y0`
    have hlab : lab G e v = y0 := by
      funext i
      cases hxi : x i with
      | none =>
        have hv : v i = if y0 i = 1 then (G.ends (e i)).2 else (G.ends (e i)).1 := by
          simp [v, hxi]
        simp only [lab, hv]
        by_cases h1 : y0 i = 1
        · simp [h1]
        · simp only [h1, if_false, if_neg (G.ne (e i))]
          exact (zmod2_eq_zero_of_ne_one _ h1).symm
      | some w =>
        have hv : v i = w := by simp [v, hxi]
        have hiZ : i ∉ Z := by rw [hmemZ, hxi]; simp
        rw [hy0out i hiZ]
        simp [lab, hv, yo, hxi]
    refine ⟨(v, ⟨fam Z, hS Z⟩), ⟨⟨?_, ?_⟩, ⟨?_, rfl⟩⟩, ?_⟩
    · intro i
      cases hxi : x i with
      | none =>
        simp only [v, hxi]
        split_ifs <;> simp
      | some w =>
        have hv : v i = w := by simp [v, hxi]
        show v i = _ ∨ v i = _
        rw [hv]; exact hend i w hxi
    · show lab G e v ∈ fam Z
      rw [hlab]; exact hy0C
    · intro i
      cases hxi : x i with
      | none => exact Or.inl rfl
      | some w => right; simp [v, hxi]
    · -- uniqueness
      rintro ⟨v', s'⟩ ⟨⟨he', hlab'⟩, ⟨hx', hs'⟩⟩
      have hs : s' = ⟨fam Z, hS Z⟩ := Subtype.ext hs'.symm
      subst hs
      have hout : ∀ i, i ∉ Z → v' i = v i := by
        intro i hi
        rw [hmemZ] at hi
        rcases hx' i with h | h
        · exact absurd h hi
        · have hv : v i = v' i := by simp [v, h]
          exact hv.symm
      have hlab'' : lab G e v' = y0 := by
        apply hy0uniq
        refine ⟨hlab', ?_⟩
        intro i hi
        have hv := hout i hi
        rw [hmemZ] at hi
        obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hi
        have : v i = w := by simp [v, hw]
        simp [lab, yo, hw, hv, this]
      have hv' : v' = v := by
        funext i
        by_cases hi : i ∈ Z
        · have hxi : x i = none := (hmemZ i).mp hi
          have hvi : v i = if y0 i = 1 then (G.ends (e i)).2 else (G.ends (e i)).1 := by
            simp [v, hxi]
          have hl := congrFun hlab'' i
          simp only [lab] at hl
          rw [hvi]
          by_cases h1 : y0 i = 1
          · rw [if_pos h1]
            by_contra hne
            rw [if_neg hne] at hl
            rw [h1] at hl
            exact absurd hl (by decide)
          · rw [if_neg h1]
            rcases he' i with h | h
            · exact h
            · rw [if_pos h] at hl
              exact absurd hl.symm h1
        · exact hout i hi
      subst hv'
      rfl

end WatsonBinaryRank
