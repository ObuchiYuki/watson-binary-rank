import Mathlib

/-!
# Definitions

* `BMat R C`: a 0/1 matrix with rows `R` and columns `C` (entries in `Bool`).
* `IsPartition T rows cols`: the rectangles `rows i × cols i` are all-ones and every one of `T`
  lies in exactly one of them.
* `BrLE T n`: `T` has such a partition with at most `n` rectangles.
* `binRank T`: the binary rank (least such `n`).
* `kronPow T k`: the `k`-fold Kronecker power, with rows `Fin k → R` and columns `Fin k → C`.
* `watsonM`: the 5 × 6 matrix of Watson (2016), proof of Theorem 2(2).
-/

namespace WatsonBinaryRank

/-- A 0/1 matrix with rows `R` and columns `C`. -/
abbrev BMat (R C : Type) := R → C → Bool

/-- The rectangles `rows i × cols i` form an exact partition of the ones of `T` into
all-ones rectangles. -/
structure IsPartition {R C ι : Type} (T : BMat R C) (rows : ι → Set R) (cols : ι → Set C) :
    Prop where
  ones : ∀ i, ∀ r ∈ rows i, ∀ c ∈ cols i, T r c = true
  cover : ∀ r c, T r c = true → ∃! i, r ∈ rows i ∧ c ∈ cols i

/-- `T` can be partitioned into at most `n` all-ones rectangles. -/
def BrLE {R C : Type} (T : BMat R C) (n : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (rows : ι → Set R) (cols : ι → Set C),
    Fintype.card ι ≤ n ∧ IsPartition T rows cols

/-- The binary rank: the least number of all-ones rectangles that partition the ones of `T`. -/
noncomputable def binRank {R C : Type} (T : BMat R C) : ℕ := sInf {n | BrLE T n}

/-- The `k`-fold Kronecker power. -/
def kronPow {R C : Type} (T : BMat R C) (k : ℕ) : BMat (Fin k → R) (Fin k → C) :=
  fun r c => decide (∀ i, T (r i) (c i) = true)

lemma kronPow_eq_true {R C : Type} (T : BMat R C) (k : ℕ) (r : Fin k → R) (c : Fin k → C) :
    kronPow T k r c = true ↔ ∀ i, T (r i) (c i) = true := by
  simp [kronPow]

/-- Watson's matrix `M` (Watson 2016, proof of Theorem 2(2)). -/
def watsonM : BMat (Fin 5) (Fin 6) :=
  ![![true,  true,  true,  false, false, false],
    ![true,  false, false, true,  true,  false],
    ![false, true,  false, true,  false, true ],
    ![false, false, true,  false, true,  true ],
    ![true,  true,  true,  true,  true,  true ]]

/-! ## Basic facts -/

section basic

variable {R C : Type}

lemma BrLE.mono {T : BMat R C} {m n : ℕ} (h : BrLE T m) (hmn : m ≤ n) : BrLE T n := by
  obtain ⟨ι, hι, rows, cols, hc, hp⟩ := h
  exact ⟨ι, hι, rows, cols, hc.trans hmn, hp⟩

/-- Pulling a partition back along maps of rows and columns. -/
lemma BrLE.comap {R' C' : Type} {T : BMat R C} {n : ℕ} (h : BrLE T n) (f : R' → R)
    (g : C' → C) : BrLE (fun r c => T (f r) (g c)) n := by
  obtain ⟨ι, hι, rows, cols, hc, hp⟩ := h
  refine ⟨ι, hι, fun i => f ⁻¹' rows i, fun i => g ⁻¹' cols i, hc, ?_, ?_⟩
  · intro i r hr c hc'
    exact hp.ones i (f r) hr (g c) hc'
  · intro r c hrc
    obtain ⟨i, hi, huniq⟩ := hp.cover (f r) (g c) hrc
    exact ⟨i, hi, fun j hj => huniq j hj⟩

/-- Every matrix with finitely many rows has a partition (one rectangle per row). -/
lemma brLE_card_rows [Fintype R] (T : BMat R C) : BrLE T (Fintype.card R) := by
  refine ⟨R, inferInstance, fun i => {i}, fun i => {c | T i c = true}, le_rfl, ?_, ?_⟩
  · intro i r hr c hc
    rw [Set.mem_singleton_iff] at hr
    subst hr; exact hc
  · intro r c hrc
    refine ⟨r, ⟨rfl, hrc⟩, ?_⟩
    rintro j ⟨hj, -⟩
    exact (Set.mem_singleton_iff.mp hj).symm

lemma binRank_le {T : BMat R C} {n : ℕ} (h : BrLE T n) : binRank T ≤ n :=
  Nat.sInf_le h

lemma le_binRank [Fintype R] {T : BMat R C} {n : ℕ} (h : ∀ m, BrLE T m → n ≤ m) :
    n ≤ binRank T :=
  h _ (Nat.sInf_mem (s := {n | BrLE T n}) ⟨_, brLE_card_rows T⟩)

end basic

end WatsonBinaryRank
