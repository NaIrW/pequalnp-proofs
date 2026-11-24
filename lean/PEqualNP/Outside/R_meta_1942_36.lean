import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1942_36
    (truncate : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∃ p l, I p l) → PEqualNP.TopForm.IsAO2 (N+N) C → (∀ z : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true)) → PEqualNP.ReadK.IsReadK (N+N) C 2 →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧ D.size ≤ 9*C.size ∧
      PEqualNP.CircuitLowerBounds.HasLineDegree (N+N) (Finset.range (N+N)) D 4 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) D = PEqualNP.MetaComplexity.circuitFun (N+N) C)
    (degreeFour : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    2 ≤ q → N = q^2+q+1 → (∀ l : Fin N, ∃ A : Finset (Fin N), A.card=q+1 ∧ ∀ p, p∈A ↔ I p l) →
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    PEqualNP.TopForm.IsAO2 (N+N) C → (∀ A : Finset (Fin (N+N)), A.card ≤ 4 →
      (PEqualNP.MetaComplexity.circuitFun (N+N) C (fun i : Fin (N+N) => decide (i∈A)) = true ↔
      ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ A ∧ Fin.natAdd N l ∈ A)) → PEqualNP.CircuitLowerBounds.HasLineDegree (N+N) (Finset.range (N+N)) C 4 →
    9*(N*q) ≤ 100*C.size) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro q N I inst C order count lines joins binary computes read
  have npos : 0<N := by omega
  let l : Fin N := ⟨0,npos⟩
  have h : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [lines]; omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  have inhabited : ∃ p l, I p l := ⟨p,l,(Finset.mem_filter.mp hp).2⟩
  obtain ⟨D, db, size, cap, eq⟩ := truncate N I C inhabited binary computes read
  have listed (l : Fin N) : ∃ A : Finset (Fin N), A.card=q+1 ∧ ∀ p, p∈A ↔ I p l :=
    ⟨Finset.univ.filter (fun p => I p l),lines l,by simp⟩
  have tested (A : Finset (Fin (N+N))) (_ : A.card≤4) :
      PEqualNP.MetaComplexity.circuitFun (N+N) D (fun i : Fin (N+N) => decide (i∈A))=true ↔
      ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ A ∧ Fin.natAdd N l ∈ A := by
    rw [eq,computes]
    simp only [decide_eq_true_eq]
  have bound := degreeFour q N I D order count listed joins db tested cap
  omega
