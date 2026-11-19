/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingIso

/-!
# LeanSMILES.Aromaticity.RingSetIso

The ring set follows a renumbering

`Work.candidateCycles` keeps one cycle per bond mask, each tagged with its mask, and every cycle
found from any root is represented (`Work.candidateCycles_spec`). Under a renumbering
(`Work.WorkIso`) each candidate matches one of the other copy, with the same ring up to start and
direction and the bonds renamed (`Work.WorkIso.candidate`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

lemma foldl_addCandidate (m : Work) : ∀ (L : List (List ℕ)) (cands : Array (ℕ × List ℕ)),
    (cands.toList.map (·.1)).Nodup → (∀ e ∈ cands.toList, e.1 = m.cycleMask e.2) →
    ((L.foldl m.addCandidate cands).toList.map (·.1)).Nodup ∧
      (∀ e ∈ (L.foldl m.addCandidate cands).toList, e.1 = m.cycleMask e.2) ∧
      (∀ e ∈ (L.foldl m.addCandidate cands).toList, e ∈ cands.toList ∨ e.2 ∈ L) ∧
      (∀ c ∈ L, ∃ e ∈ (L.foldl m.addCandidate cands).toList, e.1 = m.cycleMask c) ∧
      ∀ e ∈ cands.toList, e ∈ (L.foldl m.addCandidate cands).toList
  | [], cands, h1, h2 => ⟨h1, h2, fun e he ↦ .inl he, by simp, fun _ h ↦ h⟩
  | c :: L, cands, h1, h2 => by
    rw [List.foldl_cons]
    unfold addCandidate
    dsimp only
    split
    · rename_i hnew
      have hnew' : ∀ e ∈ cands.toList, e.1 ≠ m.cycleMask c := by
        intro e he heq
        have : cands.toList.any (fun x ↦ x.1 == m.cycleMask c) = true :=
          List.any_eq_true.2 ⟨e, he, by simp [heq]⟩
        rw [Array.any_toList] at this
        rw [this] at hnew
        cases hnew
      obtain ⟨g1, g2, g3, g4, g5⟩ := foldl_addCandidate m L (cands.push (m.cycleMask c, c))
        (by rw [Array.toList_push, List.map_append]
            refine List.nodup_append.2 ⟨h1, by simp, fun a ha b hb e ↦ ?_⟩
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 ha
            exact hnew' e0 he0 e)
        (fun e he ↦ by
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact h2 e he
          · rfl)
      refine ⟨g1, g2, fun e he ↦ ?_, fun c' hc' ↦ ?_, fun e he ↦ g5 e (by simp [he])⟩
      · rcases g3 e he with he' | he'
        · rw [Array.toList_push, List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · exact .inl he'
          · exact .inr List.mem_cons_self
        · exact .inr (List.mem_cons_of_mem _ he')
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨(m.cycleMask c', c'), g5 _ (by simp), rfl⟩
        · exact g4 c' hc'
    · rename_i hold
      obtain ⟨g1, g2, g3, g4, g5⟩ := foldl_addCandidate m L cands h1 h2
      refine ⟨g1, g2, fun e he ↦ ?_, fun c' hc' ↦ ?_, g5⟩
      · rcases g3 e he with he' | he'
        · exact .inl he'
        · exact .inr (List.mem_cons_of_mem _ he')
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · have : cands.toList.any (fun x ↦ x.1 == m.cycleMask c') = true := by
            rw [Array.any_toList]; simpa using hold
          obtain ⟨e, he, heq⟩ := List.any_eq_true.1 this
          exact ⟨e, g5 e he, by simpa using heq⟩
        · exact g4 c' hc'

/-- **The candidates**: one per mask, each tagged with its mask, each found from a root, and
every cycle found from a root represented by its mask. -/
theorem candidateCycles_spec (m : Work) :
    (m.candidateCycles.toList.map (·.1)).Nodup ∧
      (∀ e ∈ m.candidateCycles.toList, e.1 = m.cycleMask e.2 ∧
        ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) ∧
      ∀ r < m.numAtoms, ∀ c ∈ m.cyclesFrom r,
        ∃ e ∈ m.candidateCycles.toList, e.1 = m.cycleMask c := by
  unfold candidateCycles
  have key : ∀ (rs : List ℕ) (cands : Array (ℕ × List ℕ)), (∀ r ∈ rs, r < m.numAtoms) →
      (cands.toList.map (·.1)).Nodup →
      (∀ e ∈ cands.toList, e.1 = m.cycleMask e.2 ∧ ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) →
      let res := rs.foldl (fun cands r ↦ (m.cyclesFrom r).foldl m.addCandidate cands) cands
      (res.toList.map (·.1)).Nodup ∧
        (∀ e ∈ res.toList, e.1 = m.cycleMask e.2 ∧ ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) ∧
        (∀ r ∈ rs, ∀ c ∈ m.cyclesFrom r, ∃ e ∈ res.toList, e.1 = m.cycleMask c) ∧
        ∀ e ∈ cands.toList, e ∈ res.toList := by
    intro rs
    induction rs with
    | nil => intro cands _ h1 h2; exact ⟨h1, h2, by simp, fun _ h ↦ h⟩
    | cons r rs ih =>
      intro cands hrs h1 h2
      dsimp only
      rw [List.foldl_cons]
      have hr : r < m.numAtoms := hrs r List.mem_cons_self
      obtain ⟨f1, f2, f3, f4, f5⟩ := foldl_addCandidate m (m.cyclesFrom r) cands h1
        (fun e he ↦ (h2 e he).1)
      obtain ⟨i1, i2, i3, i4⟩ := ih _ (fun r hr ↦ hrs r (List.mem_cons_of_mem _ hr)) f1
        (fun e he ↦ ⟨f2 e he, by
          rcases f3 e he with he' | he'
          · exact (h2 e he').2
          · exact ⟨r, hr, he'⟩⟩)
      refine ⟨i1, i2, fun r' hr' c hc ↦ ?_, fun e he ↦ i4 e (f5 e he)⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · obtain ⟨e, he, hm⟩ := f4 c hc
        exact ⟨e, i4 e he, hm⟩
      · exact i3 r' hr' c hc
  obtain ⟨k1, k2, k3, -⟩ := key (List.range m.numAtoms) #[] (fun r hr ↦ List.mem_range.1 hr)
    (by simp) (by simp)
  exact ⟨k1, k2, fun r hr c hc ↦ k3 r (List.mem_range.2 hr) c hc⟩

end Work

end LeanSMILES.Aromaticity
