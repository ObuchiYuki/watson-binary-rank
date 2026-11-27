import WatsonBinaryRank.Count

/-!
# Main results

* `watsonM_eq`: Watson's matrix `M` is, after transposition, the matrix `incMat K₄`.
* `binRank_watson_le`: `binRank (M^{⊗33}) ≤ 4^33 · 1431`.
* `watson_conjecture_fails`: `binRank (M^{⊗33}) < 5^33`, so Watson's Conjecture 1
  (`binRank (M^{⊗k}) = 5^k` for all `k`) is false.
* `four_pow_le_binRank`: `4^k ≤ binRank (M^{⊗k})` for every `k` (fooling sets).
-/

namespace WatsonBinaryRank

open Classical

/-! ## Transposition -/

lemma BrLE.transpose {R C : Type} {T : BMat R C} {n : ℕ} (h : BrLE T n) :
    BrLE (fun c r => T r c) n := by
  obtain ⟨ι, hι, rows, cols, hc, hp⟩ := h
  refine ⟨ι, hι, cols, rows, hc, ?_, ?_⟩
  · intro i c hc' r hr; exact hp.ones i r hr c hc'
  · intro c r hrc
    obtain ⟨i, hi, huniq⟩ := hp.cover r c hrc
    exact ⟨i, ⟨hi.2, hi.1⟩, fun j hj => huniq j ⟨hj.2, hj.1⟩⟩

/-! ## The complete graph `K₄` and Watson's matrix -/

/-- `K₄` with edges `01, 02, 03, 12, 13, 23`. -/
def K4 : Graph (Fin 4) (Fin 6) where
  ends := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  ne := by decide

/-- Rows of `M` as columns of `incMat K₄`: the bottom (all-ones) row is the extra column. -/
def rowMap : Fin 5 → Option (Fin 4) := ![some 0, some 1, some 2, some 3, none]

lemma watsonM_eq : ∀ r c, watsonM r c = incMat K4 c (rowMap r) := by
  decide

lemma kronPow_watsonM (k : ℕ) :
    kronPow watsonM k = fun (r : Fin k → Fin 5) (c : Fin k → Fin 6) =>
      kronPow (incMat K4) k c (fun i => rowMap (r i)) := by
  funext r c
  simp only [kronPow, watsonM_eq]

lemma BrLE_watson_of_K4 {k n : ℕ} (h : BrLE (kronPow (incMat K4) k) n) :
    BrLE (kronPow watsonM k) n := by
  rw [kronPow_watsonM]
  exact (h.comap id (fun (r : Fin k → Fin 5) i => rowMap (r i))).transpose

/-! ## The numbers for `k = 33` -/

/-- How many parity-check matrices are used for each size `z = |Z|`. -/
def Nv (z : ℕ) : ℕ :=
  [1, 6, 14, 22, 29, 35, 41, 45, 49, 52, 54, 56, 58, 60, 61, 61, 62, 62, 61, 61, 60, 58, 56,
    54, 52, 49, 45, 41, 37, 32, 26, 19, 11, 1].getD z 0

lemma Nv_sum : ∑ z ∈ Finset.range 34, Nv z = 1431 := by decide

lemma Nv_ok_factorial : ∀ z ≤ 33,
    Nat.factorial 33 / (Nat.factorial z * Nat.factorial (33 - z)) * bad z 33 ^ Nv z <
      2 ^ (z * 33 * Nv z) := by
  decide +kernel

lemma Nv_ok : ∀ z ≤ 33, Nat.choose 33 z * bad z 33 ^ Nv z < 2 ^ (z * 33 * Nv z) := by
  intro z hz
  rw [Nat.choose_eq_factorial_div_factorial hz]
  exact Nv_ok_factorial z hz

theorem brLE_K4_33 : BrLE (kronPow (incMat K4) 33) (4 ^ 33 * 1431) := by
  have hex : ∀ z, z ≤ 33 → ∃ Hs : Fin (Nv z) → Matrix (Fin z) (Fin 33) (ZMod 2),
      ∀ Z : Finset (Fin 33), ∀ hZ : Z.card = z,
        ∃ j, (subCols (Hs j) Z (Z.orderIsoOfFin hZ).toEquiv).det ≠ 0 :=
    fun z hz => exists_good 33 z (Nv z) (Nv_ok z hz)
  choose Hs hHs using hex
  have hcard : ∀ Z : Finset (Fin 33), Z.card ≤ 33 := fun Z => by
    simpa using Finset.card_le_univ Z
  have hj : ∀ Z : Finset (Fin 33), ∃ j, (subCols (Hs Z.card (hcard Z) j) Z
      (Z.orderIsoOfFin rfl).toEquiv).det ≠ 0 := fun Z => hHs _ _ Z rfl
  choose j hj using hj
  let fam : Finset (Fin 33) → Set (Fin 33 → ZMod 2) := fun Z =>
    kerSet (Hs Z.card (hcard Z) (j Z))
  let S : Finset (Set (Fin 33 → ZMod 2)) := (Finset.range 34).biUnion fun z =>
    if h : z ≤ 33 then Finset.univ.image (fun i => kerSet (Hs z h i)) else ∅
  have hfam : ∀ Z, FaceProp (fam Z) Z := fun Z =>
    faceProp_kerSet _ Z _ (hj Z)
  have hS : ∀ Z, fam Z ∈ S := by
    intro Z
    simp only [S, Finset.mem_biUnion, Finset.mem_range]
    refine ⟨Z.card, by have := hcard Z; omega, ?_⟩
    rw [dif_pos (hcard Z)]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hScard : S.card ≤ 1431 := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← Nv_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    split_ifs with h
    · exact Finset.card_image_le.trans (by simp)
    · simp
  have := code_rule K4 33 fam hfam S hS
  simp only [Fintype.card_fin] at this
  exact this.mono (Nat.mul_le_mul_left _ hScard)

theorem binRank_watson_le : binRank (kronPow watsonM 33) ≤ 4 ^ 33 * 1431 :=
  binRank_le (BrLE_watson_of_K4 brLE_K4_33)

/-- **Watson's Conjecture 1 is false**: `binRank (M^{⊗33}) < 5^33`. -/
theorem watson_conjecture_fails : binRank (kronPow watsonM 33) < 5 ^ 33 :=
  binRank_watson_le.trans_lt (by norm_num)

/-! ## The lower bound `4^k` (fooling sets) -/

/-- A fooling set indexed by `ι`. -/
structure IsFooling {R C ι : Type} (T : BMat R C) (r : ι → R) (c : ι → C) : Prop where
  diag : ∀ j, T (r j) (c j) = true
  off : ∀ j j', j ≠ j' → T (r j) (c j') = false ∨ T (r j') (c j) = false

lemma IsFooling.card_le {R C ι : Type} [Fintype ι] {T : BMat R C} {r : ι → R} {c : ι → C}
    (hF : IsFooling T r c) {n : ℕ} (h : BrLE T n) : Fintype.card ι ≤ n := by
  obtain ⟨κ, hκ, rows, cols, hc, hp⟩ := h
  have hex := fun j => hp.cover (r j) (c j) (hF.diag j)
  choose f hf _ using hex
  refine (Fintype.card_le_of_injective f ?_).trans hc
  intro j j' hjj'
  by_contra hne
  rcases hF.off j j' hne with h0 | h0
  · have := hp.ones (f j) (r j) (hf j).1 (c j') (hjj' ▸ (hf j').2)
    rw [this] at h0; exact Bool.noConfusion h0
  · have := hp.ones (f j) (r j') (hjj' ▸ (hf j').1) (c j) (hf j).2
    rw [this] at h0; exact Bool.noConfusion h0

lemma IsFooling.kronPow {R C ι : Type} {T : BMat R C} {r : ι → R} {c : ι → C}
    (hF : IsFooling T r c) (k : ℕ) :
    IsFooling (kronPow T k) (fun (js : Fin k → ι) i => r (js i)) (fun (js : Fin k → ι) i => c (js i)) := by
  refine ⟨fun js => (kronPow_eq_true _ _ _ _).mpr fun i => hF.diag (js i), ?_⟩
  intro js js' hne
  obtain ⟨i, hi⟩ : ∃ i, js i ≠ js' i := by
    by_contra h; push Not at h; exact hne (funext h)
  rcases hF.off (js i) (js' i) hi with h0 | h0
  · left
    by_contra hk
    rw [Bool.not_eq_false, kronPow_eq_true] at hk
    rw [hk i] at h0; exact Bool.noConfusion h0
  · right
    by_contra hk
    rw [Bool.not_eq_false, kronPow_eq_true] at hk
    rw [hk i] at h0; exact Bool.noConfusion h0

/-- A fooling set of size 4 in `M` (Watson 2016). -/
lemma watson_fooling :
    IsFooling watsonM (![0, 1, 2, 3] : Fin 4 → Fin 5) (![0, 3, 1, 2] : Fin 4 → Fin 6) := by
  constructor <;> decide

theorem four_pow_le_binRank (k : ℕ) : 4 ^ k ≤ binRank (kronPow watsonM k) := by
  apply le_binRank
  intro m hm
  have := (watson_fooling.kronPow k).card_le hm
  simpa [Fintype.card_fun] using this

/-- The 5 rows of `M` give `binRank (M^{⊗k}) ≤ 5^k`. -/
theorem binRank_le_five_pow (k : ℕ) : binRank (kronPow watsonM k) ≤ 5 ^ k := by
  have := binRank_le (brLE_card_rows (kronPow watsonM k))
  simpa [Fintype.card_fun] using this

end WatsonBinaryRank
