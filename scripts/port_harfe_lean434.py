from pathlib import Path

p = Path("iod-port/FixedPointTheorems/cubical_sperner_prep.lean")
s = p.read_text()

replacements = [
    (
        "def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}",
        "noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}",
    ),
    (
        "def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )",
        "noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )",
    ),
]

for old, new in replacements:
    if s.count(old) != 1:
        raise SystemExit(f"expected exactly one occurrence: {old}")
    s = s.replace(old, new)

old = """  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    unfold ccc_fun coord_change_count
    rw [Fin.mk.inj_iff]
    have h3 : SC.n = Fintype.card (Fin SC.n) := by {exact Eq.symm (Fintype.card_fin SC.n)}
    simp only [ne_eq, Fin.val_last]
    nth_rewrite 7 [h3]
    rw [Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  }"""

new = """  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    change Finset.card {i | I 0 i ≠ I (Fin.last m) i} = SC.n ↔
      ∀ k, I 0 k ≠ I (Fin.last m) k
    rw [← Fintype.card_fin SC.n, Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  }"""

if s.count(old) != 1:
    raise SystemExit("expected original ccc_fun_case_D_iff proof exactly once")
s = s.replace(old, new)

p.write_text(s)
print("Applied Lean 4.34 compatibility patch to", p)
