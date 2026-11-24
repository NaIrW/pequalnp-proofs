import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Peel the first two gates. Wire ten in each child represents a missing input.
-- Fixing primary input four to false identifies the first wire with input zero.
-- Exactly one later gate can read primary input four, and this gate must be an OR.
-- The three searches retain this count when they supply the second signal for free.
theorem PEqualNP.Outside.R_meta_1676_43 :
    (∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      C.size ≤ 15 → C.size = 15 ∧ (C.gates.tail.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4)).length = 1 ∧
      (∀ g ∈ C.gates.tail, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = true → g.op = GateOp.or)) →
    (∀ (i : Fin 11), ¬(i = 4) → ∀ D : Circuit, FanInTwo D → D.size = 13 →
      (∀ g ∈ D.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = true → g.op = GateOp.or) →
      (D.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4)).length + (if i = 4 then 1 else 0) = 1 →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [!(w.getD i.val false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ (i j : Fin 11), i ≤ j → ¬(i = 4 ∨ j = 4) → ∀ D : Circuit, FanInTwo D → D.size = 13 →
      (∀ g ∈ D.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = true → g.op = GateOp.or) →
      (D.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4)).length + (if i = 4 ∨ j = 4 then 1 else 0) = 1 →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [(w.getD i.val false && w.getD j.val false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ (i j : Fin 11), i ≤ j → ∀ D : Circuit, FanInTwo D → D.size = 13 →
      (∀ g ∈ D.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = true → g.op = GateOp.or) →
      (D.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4)).length + (if i = 4 ∨ j = 4 then 1 else 0) = 1 →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [(w.getD i.val false || w.getD j.val false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro structural negCase andCase orCase C fan first computes
  classical
  let G := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4]
  let step := fun (s : List Bool) (g : Gate) => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]
  have preserved (gs : List Gate) (s : List Bool) (i : Nat) (hi : i < s.length) :
      (gs.foldl step s).getD i false = s.getD i false := by
    induction gs generalizing s with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have shapes : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
    g.inputs.length ≤ 2 →
    (∃ i : Fin 11, g.op ≠ .or ∧ (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = decide (i = 4) ∧
      ∀ w : List Bool, w.length = 10 →
      g.op.eval (g.inputs.map (fun n => w.getD n false)) = !(w.getD i.val false)) ∨
    (∃ i j : Fin 11, i ≤ j ∧ g.op ≠ .or ∧
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = decide (i = 4 ∨ j = 4) ∧
      ∀ w : List Bool, w.length = 10 →
      g.op.eval (g.inputs.map (fun n => w.getD n false)) = (w.getD i.val false && w.getD j.val false)) ∨
    (∃ i j : Fin 11, i ≤ j ∧
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 4 = decide (i = 4 ∨ j = 4) ∧
      ∀ w : List Bool, w.length = 10 →
      g.op.eval (g.inputs.map (fun n => w.getD n false)) = (w.getD i.val false || w.getD j.val false)) := by
    let idx (n : ℕ) : Fin 11 := if h : n < 10 then ⟨n, by omega⟩ else 10
    have idx4 (n : ℕ) : idx n = 4 ↔ n = 4 := by
      by_cases h : n < 10
      · simp [idx, h, Fin.ext_iff]
      · simp [idx, h, show n ≠ 4 by omega]
    have sentinel (w : List Bool) (hw : w.length = 10) : w.getD (10 : Fin 11).val false = false := by
      exact List.getD_eq_default w false (by change w.length ≤ 10; omega)
    have canon (n : ℕ) (w : List Bool) (hw : w.length = 10) :
        w.getD n false = w.getD (idx n).val false := by
      by_cases h : n < 10
      · simp [idx,h]
      · simp only [idx,h,dite_false]
        exact (List.getD_eq_default w false (by omega)).trans (sentinel w hw).symm
    have map_eq (xs : List ℕ) (w : List Bool) (hw : w.length = 10) :
        xs.map (fun n => w.getD n false) = xs.map (fun n => w.getD (idx n).val false) :=
      List.map_congr_left (fun n _ => canon n w hw)
    have ordered (f : Bool → Bool → Bool) (sym : ∀ x y, f x y = f y x) (a b : Fin 11) :
        ∃ i j : Fin 11, i ≤ j ∧ ((a = 4 ∨ b = 4) ↔ (i = 4 ∨ j = 4)) ∧ ∀ w : List Bool,
          f (w.getD a.val false) (w.getD b.val false) = f (w.getD i.val false) (w.getD j.val false) := by
      by_cases hab : a ≤ b
      · exact ⟨a,b,hab,Iff.rfl,fun _ => rfl⟩
      · exact ⟨b,a,le_of_not_ge hab,or_comm,fun w => sym _ _⟩
    have a1 (a : Bool) : GateOp.and.eval [a] = (a && a) := by cases a <;> rfl
    have o1 (a : Bool) : GateOp.or.eval [a] = (a || a) := by cases a <;> rfl
    have a2 (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have o2 (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    rintro ⟨op, inps⟩ hop hlen
    change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at hop
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    change inps.length ≤ 2 at hlen
    cases inps with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact Or.inl ⟨10,(by intro bad; cases bad),rfl,fun w hw => by rw [sentinel w hw]; rfl⟩
      · exact Or.inr (Or.inr ⟨10,10,le_rfl,rfl,fun w hw => by rw [sentinel w hw]; rfl⟩)
      · exact Or.inl ⟨10,(by intro bad; cases bad),rfl,fun w hw => by rw [sentinel w hw]; rfl⟩
    | cons a rest =>
      cases rest with
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨idx a,idx a,le_rfl,(by intro bad; cases bad),by change [a].contains 4 = _; simp [idx4, List.contains_eq_mem, eq_comm],fun w hw => by rw [map_eq _ w hw]; exact a1 _⟩)
        · exact Or.inr (Or.inr ⟨idx a,idx a,le_rfl,by change [a].contains 4 = _; simp [idx4, List.contains_eq_mem, eq_comm],fun w hw => by rw [map_eq _ w hw]; exact o1 _⟩)
        · exact Or.inl ⟨idx a,(by intro bad; cases bad),by change [a].contains 4 = _; simp [idx4, List.contains_eq_mem, eq_comm],fun w hw => by rw [map_eq _ w hw]; rfl⟩
      | cons b tail =>
        cases tail with
        | cons c tail => simp at hlen
        | nil =>
          rcases hop with rfl | rfl | rfl
          · obtain ⟨i,j,hij,read,eq⟩ := ordered and Bool.and_comm (idx a) (idx b)
            refine Or.inr (Or.inl ⟨i,j,hij,(by intro bad; cases bad),?_,?_⟩)
            · change [a,b].contains 4 = _
              exact (show [a,b].contains 4 = decide (idx a = 4 ∨ idx b = 4) by
                simp [idx4, List.contains_eq_mem, eq_comm]).trans (Bool.decide_congr read)
            intro w hw
            rw [map_eq _ w hw]
            exact (a2 _ _).trans (eq w)
          · obtain ⟨i,j,hij,read,eq⟩ := ordered or Bool.or_comm (idx a) (idx b)
            refine Or.inr (Or.inr ⟨i,j,hij,?_,?_⟩)
            · change [a,b].contains 4 = _
              exact (show [a,b].contains 4 = decide (idx a = 4 ∨ idx b = 4) by
                simp [idx4, List.contains_eq_mem, eq_comm]).trans (Bool.decide_congr read)
            intro w hw
            rw [map_eq _ w hw]
            exact (o2 _ _).trans (eq w)
          · exact Or.inl ⟨idx a,(by intro bad; cases bad),by change [a].contains 4 = _; simp [idx4, List.contains_eq_mem, eq_comm],fun w hw => by rw [map_eq _ w hw]; rfl⟩
  by_contra! small
  obtain ⟨exactSize,readCount,onlyOr⟩ := structural C fan first computes (by omega)
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil =>
    change 0 = 15 at exactSize
    contradiction
  | cons g gs =>
    have afterFirst (x : Fin 9 → Bool) : step (List.ofFn x) g = w x := by
      have h := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [preserved _ _ _ (by simp [step])] at h
      dsimp [step] at h ⊢
      rw [List.getD_append_right _ _ _ _ (by simp)] at h
      simp only [List.length_ofFn,Nat.sub_self,List.getD_cons_zero] at h
      exact congrArg (fun d => List.ofFn x ++ [d]) h
    cases gs with
    | nil =>
      change 1 = 15 at exactSize
      contradiction
    | cons h tail =>
      let D : Circuit := ⟨tail,o⟩
      have df : FanInTwo D := by
        intro z hz
        exact fan z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
      have ds : D.size = 13 := by
        change tail.length = 13
        change (g :: h :: tail).length = 15 at exactSize
        simp only [List.length_cons] at exactSize
        omega
      let used := fun z : Gate => (z.inputs.take (bif z.op.eval [false] then 1 else 2)).contains 4
      have cnt : ((h :: tail).filter used).length = 1 := readCount
      have tailOr : ∀ z ∈ D.gates, used z = true → z.op = GateOp.or :=
        fun z hz => onlyOr z (List.mem_cons_of_mem h hz)
      have forbid (p : Prop) [Decidable p] (other : h.op ≠ .or) (same : used h = decide p) : ¬ p := by
        intro hp
        exact other (onlyOr h List.mem_cons_self (by simpa [used,hp] using same))
      have cost (p : Prop) [Decidable p] (same : used h = decide p) :
          (D.gates.filter used).length + (if p then 1 else 0) = 1 := by
        change (tail.filter used).length + (if p then 1 else 0) = 1
        by_cases hp : p <;> simpa [List.filter_cons,same,hp] using cnt
      have good (x : Fin 9 → Bool) : D.eval (step (w x) h) = G x := by
        have cg := congrFun computes x
        change (tail.foldl step (step (step (List.ofFn x) g) h)).getD o false = G x at cg
        change (tail.foldl step (step (w x) h)).getD o false = G x
        rwa [afterFirst] at cg
      have ok := fan h (by simp)
      rcases shapes h ok.1 ok.2 with ⟨i,other,raw,eq⟩ | ⟨i,j,ord,other,raw,eq⟩ | ⟨i,j,ord,raw,eq⟩
      · obtain ⟨x,bad⟩ := negCase i (forbid _ other raw) D df ds tailOr (cost _ raw)
        have cg := good x
        dsimp [step] at cg
        rw [eq (w x) (by simp [w])] at cg
        exact bad cg
      · obtain ⟨x,bad⟩ := andCase i j ord (forbid _ other raw) D df ds tailOr (cost _ raw)
        have cg := good x
        dsimp [step] at cg
        rw [eq (w x) (by simp [w])] at cg
        exact bad cg
      · obtain ⟨x,bad⟩ := orCase i j ord D df ds tailOr (cost _ raw)
        have cg := good x
        dsimp [step] at cg
        rw [eq (w x) (by simp [w])] at cg
        exact bad cg
