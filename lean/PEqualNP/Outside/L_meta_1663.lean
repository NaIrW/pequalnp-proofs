import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp _ _ _ hmeet htriangle hsMv hpMv hpMs hvMs hvMp hsMp
  have hvMv : v ∉ L Mv := fun h => htriangle Mv ⟨h, hsMv, hpMv⟩
  have hsp : s ≠ p := by
    intro e
    exact htriangle Ms ⟨hvMs, e ▸ hpMs, hpMs⟩
  have uniqueMeet {i j a b : Fin N} (hne : i ≠ j)
      (hai : a ∈ L i) (haj : a ∈ L j) (hbi : b ∈ L i) (hbj : b ∈ L j) : a = b := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hmeet i j hne)
    have ha := Finset.mem_inter.mpr ⟨hai, haj⟩
    have hb := Finset.mem_inter.mpr ⟨hbi, hbj⟩
    rw [hc, Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  intro S hvS hsS hpS
  constructor
  · intro w W choice P hPW hbad
    have hwS : w ∉ L S := by
      rcases choice with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hsS
      · exact hpS
    have hvW : v ∈ L W := by
      rcases choice with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hvMs
      · exact hvMp
    have hWS : W ≠ S := by
      intro e
      rcases choice with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hpS (e ▸ hpMs)
      · exact hsS (e ▸ hsMp)
    have hPS := hbad.1.elim id (fun h => (hwS h.2.2.2).elim)
    have hPv := uniqueMeet hWS hPW hPS hvW hvS
    rcases hbad.2 with hPM | hne
    · exact hvMv (hPv ▸ hPM)
    · exact hne.1 hPv
  · intro w S1 hw hwS1 huniq P hPM hbad
    have hwM : w ∈ L Mv := hw.elim (fun h => h ▸ hsMv) (fun h => h ▸ hpMv)
    have hvw : v ≠ w := fun h => hvMv (h ▸ hwM)
    have hvS1 : v ∉ L S1 := fun h => hvw (huniq v (Or.inl rfl) h)
    have hMS : Mv ≠ S1 := by
      intro e
      have es := huniq s (Or.inr (Or.inl rfl)) (e ▸ hsMv)
      have ep := huniq p (Or.inr (Or.inr rfl)) (e ▸ hpMv)
      exact hsp (es.trans ep.symm)
    have hPS1 := hbad.2.elim id (fun h => (hvS1 h.2.2.2).elim)
    have hPw := uniqueMeet hMS hPM hPS1 hwM hwS1
    rcases hw with rfl | rfl
    · exact hbad.1.elim (fun h => hsS (hPw ▸ h)) (fun h => h.2.1 hPw)
    · exact hbad.1.elim (fun h => hpS (hPw ▸ h)) (fun h => h.2.2.1 hPw)
