import WatsonBinaryRank.Linear

/-!
# Counting: a short list of parity-check matrices covers every column set

For fixed `m ≤ k`, if `C(k, m) · bad^N < 2^{m k N}`, where `bad` is the number of `m × k`
matrices over `F₂` whose columns in a fixed `m`-set `Z` form a singular matrix, then there are
`N` matrices such that for every `m`-set `Z` one of them is invertible on `Z`.
-/

namespace WatsonBinaryRank

open Matrix

/-- `glAux n m = ∏_{i < m} (2^n - 2^i)`. -/
def glAux (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => glAux n m * (2 ^ n - 2 ^ m)

/-- `glc n = |GL_n(F₂)|`. -/
def glc (n : ℕ) : ℕ := glAux n n

lemma glAux_eq (n m : ℕ) : glAux n m = ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [glAux, ih, Finset.prod_range_succ]

lemma card_det_ne_zero (n : ℕ) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) // A.det ≠ 0} = glc n := by
  classical
  let e : GL (Fin n) (ZMod 2) ≃ {A : Matrix (Fin n) (Fin n) (ZMod 2) // A.det ≠ 0} :=
    { toFun := fun u => ⟨u, ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero⟩
      invFun := fun A => ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr A.2)).unit
      left_inv := fun u => Units.ext rfl
      right_inv := fun A => rfl }
  rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e, Matrix.card_GL_field, ZMod.card, glc,
    glAux_eq, Fin.prod_univ_eq_prod_range (fun i => 2 ^ n - 2 ^ i)]

/-- Number of `m × k` matrices that are singular on a fixed `m`-set of columns. -/
def bad (m k : ℕ) : ℕ := 2 ^ (m * (k - m)) * (2 ^ (m * m) - glc m)

lemma card_matrix (a b : ℕ) : Fintype.card (Matrix (Fin a) (Fin b) (ZMod 2)) = 2 ^ (a * b) := by
  rw [show Fintype.card (Matrix (Fin a) (Fin b) (ZMod 2)) = Fintype.card (Fin a → Fin b → ZMod 2)
    from rfl]
  simp [Fintype.card_fun, ZMod.card, ← pow_mul, mul_comm]

lemma card_det_eq_zero (n : ℕ) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) // A.det = 0} = 2 ^ (n * n) - glc n := by
  classical
  rw [← card_matrix n n, ← card_det_ne_zero n, ← Fintype.card_subtype_compl]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun A => by simp))

open Classical in
lemma card_sing {m k : ℕ} (Z : Finset (Fin k)) (hZ : Z.card = m) (emb : Fin m ≃ Z) :
    Fintype.card {H : Matrix (Fin m) (Fin k) (ZMod 2) // (subCols H Z emb).det = 0} =
      bad m k := by
  let e : Matrix (Fin m) (Fin k) (ZMod 2) ≃
      Matrix (Fin m) (Fin m) (ZMod 2) × (Fin m → {i : Fin k // i ∉ Z} → ZMod 2) :=
    { toFun := fun H => (subCols H Z emb, fun r i => H r i)
      invFun := fun p => fun r i =>
        if h : i ∈ Z then p.1 r (emb.symm ⟨i, h⟩) else p.2 r ⟨i, h⟩
      left_inv := fun H => by
        funext r i
        by_cases h : i ∈ Z <;> simp [h, subCols]
      right_inv := fun p => by
        rcases p with ⟨A, B⟩
        refine Prod.ext ?_ ?_
        · funext r j; simp [subCols]
        · funext r i; simp [i.2] }
  have e2 : {H : Matrix (Fin m) (Fin k) (ZMod 2) // (subCols H Z emb).det = 0} ≃
      {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.det = 0} × (Fin m → {i : Fin k // i ∉ Z} → ZMod 2) :=
    (e.subtypeEquiv (p := fun H => (subCols H Z emb).det = 0) (q := fun p => p.1.det = 0)
      (fun H => Iff.rfl)).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun A : Matrix (Fin m) (Fin m) (ZMod 2) => A.det = 0))
  rw [Fintype.card_congr e2, Fintype.card_prod, card_det_eq_zero, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_fin, ZMod.card, bad]
  have hc : Fintype.card {i : Fin k // i ∈ Z} = m := by simp [hZ]
  rw [hc, Fintype.card_fin, ← pow_mul, mul_comm (k - m) m, Nat.mul_comm]

open Classical in
theorem exists_good (k m N : ℕ) (h : Nat.choose k m * bad m k ^ N < 2 ^ (m * k * N)) :
    ∃ Hs : Fin N → Matrix (Fin m) (Fin k) (ZMod 2),
      ∀ Z : Finset (Fin k), ∀ hZ : Z.card = m,
        ∃ j, (subCols (Hs j) Z (Z.orderIsoOfFin hZ).toEquiv).det ≠ 0 := by
  by_contra hne
  push Not at hne
  let B : Finset (Fin k) → Finset (Fin N → Matrix (Fin m) (Fin k) (ZMod 2)) := fun Z =>
    Finset.univ.filter (fun Hs => ∃ hZ : Z.card = m,
      ∀ j, (subCols (Hs j) Z (Z.orderIsoOfFin hZ).toEquiv).det = 0)
  have hsub : (Finset.univ : Finset (Fin N → Matrix (Fin m) (Fin k) (ZMod 2))) ⊆
      (Finset.powersetCard m Finset.univ).biUnion B := by
    intro Hs _
    obtain ⟨Z, hZ, hall⟩ := hne Hs
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨Z, hZ, by simp [B]; exact ⟨hZ, hall⟩⟩
  have hB : ∀ Z ∈ Finset.powersetCard m (Finset.univ : Finset (Fin k)),
      (B Z).card = bad m k ^ N := by
    intro Z hZmem
    have hZ : Z.card = m := (Finset.mem_powersetCard.mp hZmem).2
    have : B Z = Finset.univ.filter (fun Hs : Fin N → Matrix (Fin m) (Fin k) (ZMod 2) =>
        ∀ j, (subCols (Hs j) Z (Z.orderIsoOfFin hZ).toEquiv).det = 0) := by
      ext Hs; simp [B, hZ]
    rw [this, ← Fintype.card_subtype,
      Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ H =>
        (subCols H Z (Z.orderIsoOfFin hZ).toEquiv).det = 0)),
      Fintype.card_fun, Fintype.card_fin, card_sing Z hZ]
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [Finset.sum_congr rfl hB, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_fun, card_matrix,
    Fintype.card_fin, ← pow_mul] at hcard
  omega

end WatsonBinaryRank
