import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1197_aux

inductive Node (n k : Nat) where
  | base (u : Fin n)
  | outCopy (e : Fin k)
  | inCopy (e : Fin k)
  | arcSlot (e : Fin k)
  deriving DecidableEq

def nodeToFin {n k : Nat} : Node n k → Fin (n + 3 * k)
  | .base u => ⟨u.val, by omega⟩
  | .outCopy e => ⟨n + e.val, by omega⟩
  | .inCopy e => ⟨n + k + e.val, by omega⟩
  | .arcSlot e => ⟨n + 2 * k + e.val, by omega⟩

def finToNode {n k : Nat} (i : Fin (n + 3 * k)) : Node n k :=
  if h1 : i.val < n then .base ⟨i.val, h1⟩
  else if h2 : i.val < n + k then .outCopy ⟨i.val - n, by omega⟩
  else if h3 : i.val < n + 2 * k then .inCopy ⟨i.val - (n + k), by omega⟩
  else .arcSlot ⟨i.val - (n + 2 * k), by omega⟩

def nodeEquiv (n k : Nat) : Node n k ≃ Fin (n + 3 * k) where
  toFun := nodeToFin
  invFun := finToNode
  left_inv := by
    intro p
    cases p with
    | base u =>
      dsimp only [nodeToFin, finToNode]
      rw [dite_eq_left u.isLt]
    | outCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1; apply Fin.ext; change n + e.val - n = e.val; omega
    | inCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1; apply Fin.ext; change n + k + e.val - (n + k) = e.val; omega
    | arcSlot e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
      congr 1; apply Fin.ext; change n + 2 * k + e.val - (n + 2 * k) = e.val; omega
  right_inv := by
    intro i
    have := i.isLt
    dsimp only [finToNode]
    split_ifs <;> apply Fin.ext <;> dsimp only [nodeToFin] <;> omega

def owner {n k : Nat} (src dst : Fin k → Fin n) : Node n k → Option (Fin n)
  | .base w => some w
  | .outCopy e => some (src e)
  | .inCopy e => some (dst e)
  | .arcSlot _ => none

def ringList {n k : Nat} (src dst : Fin k → Fin n) (w : Fin n) : List (Node n k) :=
  [.base w] ++
  ((List.finRange k).filter (fun e => decide (src e = w))).map Node.outCopy ++
  ((List.finRange k).filter (fun e => decide (dst e = w))).map Node.inCopy

lemma mem_ringList_iff {n k : Nat} (src dst : Fin k → Fin n)
    (w : Fin n) (p : Node n k) :
    p ∈ ringList src dst w ↔ owner src dst p = some w := by
  cases p <;> simp [ringList, owner]

lemma ringList_nodup {n k : Nat} (src dst : Fin k → Fin n) (w : Fin n) :
    (ringList src dst w).Nodup := by
  have hnd1 : (((List.finRange k).filter (fun e => decide (src e = w))).map (@Node.outCopy n k)).Nodup :=
    ((List.nodup_finRange k).filter _).map (fun _ _ h => by cases h; rfl)
  have hnd2 : (((List.finRange k).filter (fun e => decide (dst e = w))).map (@Node.inCopy n k)).Nodup :=
    ((List.nodup_finRange k).filter _).map (fun _ _ h => by cases h; rfl)
  dsimp only [ringList]
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨by simp, hnd1, ?_⟩, hnd2, ?_⟩
  · intro p hp q hq
    rcases List.mem_map.mp hq with ⟨e, _, rfl⟩
    simp at hp
    subst p
    intro h
    cases h
  · intro p hp q hq
    rcases List.mem_map.mp hq with ⟨e, _, rfl⟩
    rcases List.mem_append.mp hp with hp | hp
    · simp at hp
      subst p
      intro h
      cases h
    · rcases List.mem_map.mp hp with ⟨e', _, rfl⟩
      intro h
      cases h

def listNext {α : Type*} [DecidableEq α] (L : List α) (p : α) : Option α :=
  if h2 : 2 ≤ L.length then
    if hmem : p ∈ L then
      let idx := L.idxOf p
      some (L[(idx + 1) % L.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

def listPrev {α : Type*} [DecidableEq α] (L : List α) (p : α) : Option α :=
  if h2 : 2 ≤ L.length then
    if hmem : p ∈ L then
      let idx := L.idxOf p
      some (L[(idx + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

lemma listNext_iff_listPrev {α : Type*} [DecidableEq α] (L : List α) (hnd : L.Nodup) (p q : α) :
    listNext L p = some q ↔ listPrev L q = some p := by
  dsimp only [listNext, listPrev]
  by_cases h2 : 2 ≤ L.length
  · rw [dite_eq_left h2, dite_eq_left h2]
    constructor
    · intro h
      by_cases hp : p ∈ L
      · rw [dite_eq_left hp] at h
        have hq_eq : L[(L.idxOf p + 1) % L.length]'(Nat.mod_lt _ (by omega)) = q :=
          Option.some.inj h
        have hq : q ∈ L := hq_eq ▸ List.getElem_mem _
        rw [dite_eq_left hq]
        congr 1
        have hp_idx : L.idxOf p < L.length := List.idxOf_lt_length_of_mem hp
        have hq_idx : L.idxOf q = (L.idxOf p + 1) % L.length := by
          rw [← hq_eq]
          exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((L.idxOf p + 1) % L.length + L.length - 1) % L.length = L.idxOf p := by
          by_cases hlast : L.idxOf p + 1 = L.length
          · rw [hlast, Nat.mod_self, zero_add]
            have : L.length - 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt this]; omega
          · have hlt : L.idxOf p + 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have heq : L.idxOf p + 1 + L.length - 1 = L.idxOf p + L.length := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hp_idx]
        have hget : L[(L.idxOf q + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)) =
            L[L.idxOf p]'hp_idx := by
          simp only [hq_idx, hmod]
        rw [hget]
        exact List.getElem_idxOf hp_idx
      · rw [dite_eq_right hp] at h; cases h
    · intro h
      by_cases hq : q ∈ L
      · rw [dite_eq_left hq] at h
        have hp_eq : L[(L.idxOf q + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)) = p :=
          Option.some.inj h
        have hp : p ∈ L := hp_eq ▸ List.getElem_mem _
        rw [dite_eq_left hp]
        congr 1
        have hq_idx : L.idxOf q < L.length := List.idxOf_lt_length_of_mem hq
        have hp_idx : L.idxOf p = (L.idxOf q + L.length - 1) % L.length := by
          rw [← hp_eq]
          exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((L.idxOf q + L.length - 1) % L.length + 1) % L.length = L.idxOf q := by
          by_cases hzero : L.idxOf q = 0
          · rw [hzero, zero_add]
            have hlt : L.length - 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have heq : L.length - 1 + 1 = L.length := by omega
            rw [heq, Nat.mod_self]
          · have hpos : 1 ≤ L.idxOf q := by omega
            have hlt1 : L.idxOf q - 1 < L.length := by omega
            have heq : L.idxOf q + L.length - 1 = (L.idxOf q - 1) + L.length := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
            have heq2 : L.idxOf q - 1 + 1 = L.idxOf q := by omega
            rw [heq2, Nat.mod_eq_of_lt hq_idx]
        have hget : L[(L.idxOf p + 1) % L.length]'(Nat.mod_lt _ (by omega)) =
            L[L.idxOf q]'hq_idx := by
          simp only [hp_idx, hmod]
        rw [hget]
        exact List.getElem_idxOf hq_idx
      · rw [dite_eq_right hq] at h; cases h
  · rw [dite_eq_right h2, dite_eq_right h2]
    simp

def ringNext {n k : Nat} (src dst : Fin k → Fin n) (p : Node n k) :
    Option (Node n k) :=
  match owner src dst p with
  | some w => listNext (ringList src dst w) p
  | none => none

def ringPrev {n k : Nat} (src dst : Fin k → Fin n) (p : Node n k) :
    Option (Node n k) :=
  match owner src dst p with
  | some w => listPrev (ringList src dst w) p
  | none => none

lemma ringNext_owner {n k : Nat} (src dst : Fin k → Fin n)
    (p q : Node n k) (h : ringNext src dst p = some q) :
    ∃ w, owner src dst p = some w ∧ owner src dst q = some w := by
  dsimp only [ringNext] at h
  cases hw : owner src dst p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listNext] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst w q).mp hq_mem⟩

lemma ringPrev_owner {n k : Nat} (src dst : Fin k → Fin n)
    (p q : Node n k) (h : ringPrev src dst p = some q) :
    ∃ w, owner src dst p = some w ∧ owner src dst q = some w := by
  dsimp only [ringPrev] at h
  cases hw : owner src dst p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listPrev] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst w q).mp hq_mem⟩

lemma ringNext_iff_ringPrev {n k : Nat} (src dst : Fin k → Fin n)
    (p q : Node n k) :
    ringNext src dst p = some q ↔ ringPrev src dst q = some p := by
  constructor
  · intro h
    rcases ringNext_owner src dst p q h with ⟨w, hwp, hwq⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwp] at h
    rw [hwq]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst w) p q).mp h
  · intro h
    rcases ringPrev_owner src dst q p h with ⟨w, hwq, hwp⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwq] at h
    rw [hwp]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst w) p q).mpr h

def ringNb {n k : Nat} (src dst : Fin k → Fin n) :
    Node n k × Bool → Option (Node n k × Bool)
  | (p, true) => (ringNext src dst p).map (fun q => (q, false))
  | (p, false) => (ringPrev src dst p).map (fun q => (q, true))

lemma ringNb_symm {n k : Nat} (src dst : Fin k → Fin n)
    (u v : Node n k × Bool) :
    ringNb src dst u = some v ↔ ringNb src dst v = some u := by
  rcases u with ⟨p, b⟩
  rcases v with ⟨q, c⟩
  cases b <;> cases c <;> simp [ringNb, ringNext_iff_ringPrev]

lemma ringNb_ne_self {n k : Nat} (src dst : Fin k → Fin n)
    (u : Node n k × Bool) :
    ringNb src dst u ≠ some u := by
  rcases u with ⟨p, b⟩
  cases b <;> simp [ringNb]

def attached {n k : Nat} (a b : Fin k → Bool) :
    Node n k × Bool → Finset (Node n k × Bool)
  | (.base _, _) => ∅
  | (.outCopy e, c) => {(.arcSlot e, !c)}
  | (.inCopy e, c) => if c = b e then {(.arcSlot e, a e)} else ∅
  | (.arcSlot e, c) =>
      {(.outCopy e, !c)} ∪ (if c = a e then {(.inCopy e, b e)} else ∅)

lemma attached_symm {n k : Nat} (a b : Fin k → Bool) (p q : Node n k × Bool) :
    q ∈ attached a b p ↔ p ∈ attached a b q := by
  have step : ∀ (p q : Node n k × Bool), q ∈ attached a b p → p ∈ attached a b q := by
    rintro ⟨p,c⟩ q h
    cases p with
    | base i => simp [attached] at h
    | outCopy e =>
      have hq : q = (Node.arcSlot e,!c) := Finset.mem_singleton.mp h
      subst q
      simp [attached]
    | inCopy e =>
      simp only [attached] at h
      split_ifs at h with hb
      · have hq := Finset.mem_singleton.mp h
        subst q
        simp [attached, hb]
      · simp at h
    | arcSlot e =>
      simp only [attached, Finset.mem_union] at h
      rcases h with h | h
      · have hq := Finset.mem_singleton.mp h
        subst q
        simp [attached]
      · split_ifs at h with ha
        · have hq := Finset.mem_singleton.mp h
          subst q
          simp [attached, ha]
        · simp at h
  exact ⟨step p q, step q p⟩

lemma attached_ne_self {n k : Nat} (a b : Fin k → Bool) (p : Node n k × Bool) :
    p ∉ attached a b p := by
  rcases p with ⟨p, c⟩
  cases p <;> simp [attached] <;> split_ifs <;> simp_all

lemma attached_same {n k : Nat} (a b : Fin k → Bool) (p q : Node n k) (c : Bool)
    (h : (q,c) ∈ attached a b (p,c)) :
    ∃ e, a e = c ∧ b e = c ∧ (Node.arcSlot e = p ∨ Node.arcSlot e = q) := by
  cases p with
  | base i => simp [attached] at h
  | outCopy e => cases c <;> simp [attached] at h
  | inCopy e =>
    simp only [attached] at h
    split_ifs at h with hb
    · have hq : q = Node.arcSlot e := congrArg Prod.fst (Finset.mem_singleton.mp h)
      have ha : c = a e := congrArg Prod.snd (Finset.mem_singleton.mp h)
      exact ⟨e, ha.symm, hb.symm, Or.inr hq.symm⟩
    · simp at h
  | arcSlot e =>
    have hs := (attached_symm a b _ _).mp h
    cases q with
    | base i => simp [attached] at hs
    | outCopy d => cases c <;> simp [attached] at hs
    | arcSlot d =>
      simp [attached] at h
      split_ifs at h <;> simp_all
    | inCopy d =>
      simp only [attached] at hs
      split_ifs at hs with hb
      · have hp : Node.arcSlot e = Node.arcSlot d := congrArg Prod.fst
          (Finset.mem_singleton.mp hs)
        have ha : c = a d := congrArg Prod.snd (Finset.mem_singleton.mp hs)
        exact ⟨d, ha.symm, hb.symm, Or.inl hp.symm⟩
      · simp at hs

def nbNode {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p : Node n k × Bool) : Finset (Node n k × Bool) :=
  {(p.1, !p.2)} ∪ (ringNb src dst p).toFinset ∪ attached a b p

lemma nb_parts {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p q : Node n k × Bool) :
    q ∈ nbNode src dst a b p ↔
      (q = (p.1, !p.2) ∨ ringNb src dst p = some q) ∨ q ∈ attached a b p := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]

lemma nbNode_card_le {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p : Node n k × Bool) : (nbNode src dst a b p).card ≤ 3 := by
  have h1 : ({(p.1, !p.2)} : Finset (Node n k × Bool)).card = 1 := Finset.card_singleton _
  have h2 : (ringNb src dst p).toFinset.card ≤ 1 := by
    cases ringNb src dst p <;> simp
  have hu1 := Finset.card_union_le ({(p.1, !p.2)} ∪ (ringNb src dst p).toFinset)
    (attached a b p)
  have hu2 := Finset.card_union_le ({(p.1, !p.2)} : Finset (Node n k × Bool))
    (ringNb src dst p).toFinset
  dsimp only [nbNode]
  rcases p with ⟨p, c⟩
  cases p with
  | base i =>
    have h3 : (attached a b (Node.base i, c)).card ≤ 1 := by simp [attached]
    omega
  | outCopy e =>
    have h3 : (attached a b (@Node.outCopy n k e, c)).card ≤ 1 := by simp [attached]
    omega
  | inCopy e =>
    have h3 : (attached a b (@Node.inCopy n k e, c)).card ≤ 1 := by
      simp only [attached]
      split_ifs <;> simp
    omega
  | arcSlot e =>
    have hr : (ringNb src dst (Node.arcSlot e, c)).toFinset.card = 0 := by
      cases c <;> simp [ringNb, ringNext, ringPrev, owner]
    have h3 : (attached a b (@Node.arcSlot n k e, c)).card ≤ 2 := by
      simp only [attached]
      split_ifs
      · exact (Finset.card_union_le _ _).trans (by simp)
      · simp
    omega

lemma nbNode_not_mem_self {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p : Node n k × Bool) : p ∉ nbNode src dst a b p := by
  rw [nb_parts]
  rintro ((h | h) | h)
  · rcases p with ⟨p,c⟩
    have hx : c = !c := congrArg Prod.snd h
    cases c <;> cases hx
  · exact ringNb_ne_self src dst p h
  · exact attached_ne_self a b p h

lemma nbNode_symm {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p q : Node n k × Bool) : q ∈ nbNode src dst a b p ↔ p ∈ nbNode src dst a b q := by
  simp only [nb_parts]
  have h1 : q = (p.1, !p.2) ↔ p = (q.1, !q.2) := by
    rcases p with ⟨p, c⟩
    rcases q with ⟨q, d⟩
    cases c <;> cases d <;> simp [eq_comm]
  rw [h1, ringNb_symm, attached_symm]

lemma nbNode_same {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (p q : Node n k) (c : Bool) (h : (q,c) ∈ nbNode src dst a b (p,c)) :
    ∃ e, a e = c ∧ b e = c ∧ (Node.arcSlot e = p ∨ Node.arcSlot e = q) := by
  rcases (nb_parts _ _ _ _ _ _).mp h with (h | h) | h
  · have hx : c = !c := congrArg Prod.snd h
    cases c <;> cases hx
  · cases c <;> simp [ringNb] at h
  · exact attached_same a b p q c h

def Sat {n k : Nat} (src dst : Fin k → Fin n) (a b z : Fin k → Bool)
    (y : Fin n → Bool) : Prop :=
  ∀ e, z e = true → ¬ (y (src e) = a e ∧ y (dst e) = b e)

def Valid {n k : Nat} (src dst : Fin k → Fin n) (a b z : Fin k → Bool)
    (x : Node n k × Bool → Bool) : Prop :=
  (∀ p q, q ∈ nbNode src dst a b p → x p = true ∨ x q = true) ∧
  (∀ e, xor (x (.arcSlot e,false)) (x (.arcSlot e,true)) = z e) ∧
  (∀ p, (∀ e, Node.arcSlot e ≠ p) → xor (x (p,false)) (x (p,true)) = true)

def readValues {n k : Nat} (x : Node n k × Bool → Bool) (i : Fin n) : Bool :=
  x (.base i,false)

def liftValues {n k : Nat} (src dst : Fin k → Fin n) (z : Fin k → Bool)
    (y : Fin n → Bool) : Node n k × Bool → Bool
  | (.base i,c) => xor (y i) c
  | (.outCopy e,c) => xor (y (src e)) c
  | (.inCopy e,c) => xor (y (dst e)) c
  | (.arcSlot e,c) => if z e then xor (y (src e)) c else true

private lemma xorPair (f t : Bool) (h : xor f t = true) : t = !f := by
  cases f <;> cases t <;> simp_all

private lemma offPair (f t : Bool) (h : xor f t = false)
    (hc : f = true ∨ t = true) : f = true ∧ t = true := by
  cases f <;> cases t <;> simp_all

private lemma pairCopy (s0 s1 u0 u1 : Bool) (hs : xor s0 s1 = true) (hu : xor u0 u1 = true)
    (e0 : s0 = true ∨ u1 = true) (e1 : s1 = true ∨ u0 = true) : s0 = u0 := by
  rw [xorPair s0 s1 hs] at e1
  rw [xorPair u0 u1 hu] at e0
  cases s0 <;> cases u0 <;> simp_all

private lemma clauseTest (x y a b : Bool) :
    (xor x a = true ∨ xor y b = true) ↔ ¬ (x = a ∧ y = b) := by
  cases x <;> cases y <;> cases a <;> cases b <;> decide

private lemma litCover (v c : Bool) : xor v c = true ∨ xor v (!c) = true := by
  cases v <;> cases c <;> decide

lemma lift_owner {n k : Nat} (src dst : Fin k → Fin n) (z : Fin k → Bool)
    (y : Fin n → Bool) (p : Node n k) (w : Fin n) (c : Bool)
    (h : owner src dst p = some w) : liftValues src dst z y (p,c) = xor (y w) c := by
  cases p <;> simp [owner] at h <;> subst w <;> rfl

lemma liftValid {n k : Nat} (src dst : Fin k → Fin n) (a b z : Fin k → Bool)
    (y : Fin n → Bool) (hy : Sat src dst a b z y) :
    Valid src dst a b z (liftValues src dst z y) := by
  let x := liftValues src dst z y
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨p,c⟩ ⟨q,d⟩ h
    rcases (nb_parts _ _ _ _ _ _).mp h with (h | h) | h
    · have hq : q = p := congrArg Prod.fst h
      have hd : d = !c := congrArg Prod.snd h
      subst q
      subst d
      cases p with
      | base i => exact litCover _ _
      | outCopy e => exact litCover _ _
      | inCopy e => exact litCover _ _
      | arcSlot e =>
        cases hz : z e
        · simp [liftValues, hz]
        · simpa only [liftValues, hz, ite_true] using litCover (y (src e)) c
    · cases c
      · simp only [ringNb, Option.map_eq_some_iff] at h
        rcases h with ⟨q', hp, heq⟩
        have hq : q' = q := congrArg Prod.fst heq
        have hd : true = d := congrArg Prod.snd heq
        subst q
        subst d
        rcases ringPrev_owner src dst _ _ hp with ⟨w, hwp, hwq⟩
        rw [lift_owner src dst z y _ _ _ hwp, lift_owner src dst z y _ _ _ hwq]
        exact litCover _ false
      · simp only [ringNb, Option.map_eq_some_iff] at h
        rcases h with ⟨q', hp, heq⟩
        have hq : q' = q := congrArg Prod.fst heq
        have hd : false = d := congrArg Prod.snd heq
        subst q
        subst d
        rcases ringNext_owner src dst _ _ hp with ⟨w, hwp, hwq⟩
        rw [lift_owner src dst z y _ _ _ hwp, lift_owner src dst z y _ _ _ hwq]
        exact litCover _ true
    · have slot_out (e : Fin k) (t : Bool) :
          x (.arcSlot e,t) = true ∨ x (.outCopy e,!t) = true := by
        cases hz : z e
        · left
          simp [x, liftValues, hz]
        · simpa [x, liftValues, hz] using litCover (y (src e)) t
      have slot_in (e : Fin k) :
          x (.arcSlot e,a e) = true ∨ x (.inCopy e,b e) = true := by
        cases hz : z e
        · left
          simp [x, liftValues, hz]
        · simpa [x, liftValues, hz] using (clauseTest _ _ _ _).mpr (hy e hz)
      change x (p,c) = true ∨ x (q,d) = true
      cases p with
      | base i => simp [attached] at h
      | outCopy e =>
        have h' : (q,d) = (Node.arcSlot e,!c) := Finset.mem_singleton.mp h
        rw [h']
        simpa using (slot_out e (!c)).symm
      | inCopy e =>
        simp only [attached] at h
        split_ifs at h with hb
        · rw [Finset.mem_singleton.mp h, hb]
          exact (slot_in e).symm
        · simp at h
      | arcSlot e =>
        simp only [attached, Finset.mem_union] at h
        rcases h with h | h
        · rw [Finset.mem_singleton.mp h]
          exact slot_out e c
        · split_ifs at h with ha
          · rw [Finset.mem_singleton.mp h, ha]
            exact slot_in e
          · simp at h
  · intro e
    cases hz : z e <;> cases hyx : y (src e) <;> simp [liftValues, hz, hyx]
  · intro p hs
    cases p with
    | base i => cases h : y i <;> simp [liftValues, h]
    | outCopy e => cases h : y (src e) <;> simp [liftValues, h]
    | inCopy e => cases h : y (dst e) <;> simp [liftValues, h]
    | arcSlot e => exact (hs e rfl).elim

lemma recover_valid {n k : Nat} (src dst : Fin k → Fin n) (a b z : Fin k → Bool)
    (xN : Node n k × Bool → Bool) (hx : Valid src dst a b z xN) :
    Sat src dst a b z (readValues xN) ∧
      xN = liftValues src dst z (readValues xN) := by
  rcases hx with ⟨hcov, hslot, hns⟩
  have hring_step (w : Fin n) (p q : Node n k) (hp : owner src dst p = some w)
      (hn : ringNext src dst p = some q) (hpf : xN (p,false) = true) :
      xN (q,false) = true := by
    have hpns : ∀ e, Node.arcSlot e ≠ p := by
      intro e h
      subst p
      simp [owner] at hp
    have hpt := xorPair _ _ (hns p hpns)
    rw [hpf] at hpt
    have hm : (q,false) ∈ nbNode src dst a b (p,true) := by
      simp [nb_parts, ringNb, hn]
    rcases hcov _ _ hm with he | he
    · rw [hpt] at he
      cases he
    · exact he
  have hring_all : ∀ (w : Fin n) (p q : Node n k),
      owner src dst p = some w → owner src dst q = some w →
      xN (p, false) = true → xN (q, false) = true := by
    intro w p q hwp hwq hpf
    let L := ringList src dst w
    have hpL : p ∈ L := (mem_ringList_iff src dst w p).mpr hwp
    have hqL : q ∈ L := (mem_ringList_iff src dst w q).mpr hwq
    by_cases h2 : 2 ≤ L.length
    · have hwalk_idx : ∀ (d : Nat) (i : Nat) (hi : i < L.length),
          xN (L[i]'hi, false) = true →
          xN (L[(i + d) % L.length]'(Nat.mod_lt _ (by omega)), false) = true := by
        intro d
        induction d with
        | zero =>
          intro i hi hxi
          simpa [Nat.mod_eq_of_lt hi] using hxi
        | succ d ih =>
          intro i hi hxi
          let j := (i + d) % L.length
          have hj : j < L.length := Nat.mod_lt _ (by omega)
          have hxj : xN (L[j]'hj, false) = true := ih i hi hxi
          have hown_j : owner src dst (L[j]'hj) = some w :=
            (mem_ringList_iff src dst w _).mp (List.getElem_mem hj)
          have hidx_j : L.idxOf (L[j]'hj) = j :=
            List.Nodup.idxOf_getElem (ringList_nodup src dst w) j hj
          have hnext_j : ringNext src dst (L[j]'hj) =
              some (L[(j + 1) % L.length]'(Nat.mod_lt _ (by omega))) := by
            dsimp only [ringNext]
            rw [hown_j]
            change listNext L (L[j]'hj) = _
            dsimp only [listNext]
            rw [dite_eq_left h2, dite_eq_left (List.getElem_mem hj)]
            simp only [hidx_j]
          have hres := hring_step w _ _ hown_j hnext_j hxj
          have hmod_eq : (j + 1) % L.length = (i + (d + 1)) % L.length := by
            dsimp only [j]
            rw [Nat.mod_add_mod, add_assoc]
          simpa only [hmod_eq] using hres
      have hp_idx : L.idxOf p < L.length := List.idxOf_lt_length_of_mem hpL
      have hq_idx : L.idxOf q < L.length := List.idxOf_lt_length_of_mem hqL
      let d := (L.idxOf q + L.length - L.idxOf p) % L.length
      have hstart : xN (L[L.idxOf p]'hp_idx, false) = true := by
        simpa [List.getElem_idxOf hp_idx] using hpf
      have hres := hwalk_idx d (L.idxOf p) hp_idx hstart
      have hmod_end : (L.idxOf p + d) % L.length = L.idxOf q := by
        dsimp only [d]
        rw [Nat.add_mod_mod]
        have heq : L.idxOf p + (L.idxOf q + L.length - L.idxOf p) = L.idxOf q + L.length := by
          omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hq_idx]
      have hres' : xN (L[L.idxOf q]'hq_idx, false) = true := by
        simpa only [hmod_end] using hres
      simpa [List.getElem_idxOf hq_idx] using hres'
    · have hlen1 : L.length = 1 := by
        have hpos : 0 < L.length := List.length_pos_of_mem hpL
        omega
      cases hL : L with
      | nil => simp [hL] at hlen1
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hL] at hpL hqL
          simp at hpL hqL
          subst hpL; subst hqL
          exact hpf
        | cons b tl2 => simp [hL] at hlen1
  have owned (p : Node n k) (w : Fin n) (c : Bool) (hp : owner src dst p = some w) :
      xN (p,c) = xor (readValues xN w) c := by
    have hbase : owner src dst (.base w) = some w := rfl
    have hf : xN (p,false) = xN (.base w,false) := by
      have h1 := hring_all w p (.base w) hp hbase
      have h2 := hring_all w (.base w) p hbase hp
      cases h1f : xN (p,false) <;> cases h2f : xN (.base w,false) <;> simp_all
    have hpns : ∀ e, Node.arcSlot e ≠ p := by
      intro e h
      subst p
      simp [owner] at hp
    cases c
    · simpa [readValues] using hf
    · rw [xorPair _ _ (hns p hpns), hf, readValues]
      generalize xN (.base w,false) = v
      cases v <;> rfl
  have slot_on (e : Fin k) (he : z e = true) (c : Bool) :
      xN (.arcSlot e,c) = xor (readValues xN (src e)) c := by
    have hs : xor (xN (.arcSlot e,false)) (xN (.arcSlot e,true)) = true := (hslot e).trans he
    have hu := hns (Node.outCopy e) (by intro f h; cases h)
    have e0 : xN (.arcSlot e,false) = true ∨ xN (.outCopy e,true) = true :=
      hcov _ _ (by simp [nb_parts, attached])
    have e1 : xN (.arcSlot e,true) = true ∨ xN (.outCopy e,false) = true :=
      hcov _ _ (by simp [nb_parts, attached])
    have hf := pairCopy _ _ _ _ hs hu e0 e1
    cases c
    · exact hf.trans (owned (.outCopy e) (src e) false rfl)
    · rw [xorPair _ _ hs, hf, ← xorPair _ _ hu]
      exact owned (.outCopy e) (src e) true rfl
  constructor
  · intro e he
    have h := hcov (.arcSlot e,a e) (.inCopy e,b e) (by simp [nb_parts, attached])
    rw [slot_on e he, owned (.inCopy e) (dst e) (b e) rfl] at h
    exact (clauseTest _ _ _ _).mp h
  · funext p
    rcases p with ⟨p,c⟩
    cases p with
    | base i => exact owned (.base i) i c rfl
    | outCopy e => exact owned (.outCopy e) (src e) c rfl
    | inCopy e => exact owned (.inCopy e) (dst e) c rfl
    | arcSlot e =>
      cases hz : z e
      · have he := hcov (.arcSlot e,false) (.arcSlot e,true) (by simp [nb_parts])
        have h := offPair _ _ ((hslot e).trans hz) he
        cases c
        · simpa [liftValues, hz] using h.1
        · simpa [liftValues, hz] using h.2
      · simpa [liftValues, hz] using slot_on e hz c

end PEqualNP.Outside.L_lib_1197_aux

open PEqualNP.Outside.L_lib_1197_aux in
theorem PEqualNP.Outside.L_lib_1197 :
∀ (n k : Nat) (u v : Fin k → Fin n) (a b : Fin k → Bool),
  ∃ (m : Nat) (slot : Fin k ↪ Fin m) (read : Fin n ↪ Fin m)
    (nb : (Fin m × Bool) → Finset (Fin m × Bool)),
    m ≤ n+3*k ∧ (∀ i e, read i ≠ slot e) ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧ (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∀ c i j, (j,c) ∈ nb (i,c) → ∃ e, a e = c ∧ b e = c ∧ (slot e = i ∨ slot e = j)) ∧
    ∀ z : Fin k → Bool,
      let sat := fun (y : Fin n → Bool) => ∀ e, z e = true → ¬ (y (u e) = a e ∧ y (v e) = b e)
      let phys := fun (x : (Fin m × Bool) → Bool) =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
        (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
      let decode := fun (x : (Fin m × Bool) → Bool) (i : Fin n) => x (read i,false)
      (∀ x, phys x → sat (decode x)) ∧
      (∀ y, sat y → ∃! x, phys x ∧ decode x = y) := by
  intro n k u v a b
  let m := n + 3 * k
  let eqN := nodeEquiv n k
  let eqP := eqN.prodCongr (Equiv.refl Bool)
  let slot : Fin k ↪ Fin m :=
    ⟨fun e => eqN (.arcSlot e), fun _ _ h => by
      have hp := eqN.injective h
      cases hp
      rfl⟩
  let read : Fin n ↪ Fin m :=
    ⟨fun i => eqN (.base i), fun _ _ h => by
      have hp := eqN.injective h
      cases hp
      rfl⟩
  let nb : (Fin m × Bool) → Finset (Fin m × Bool) :=
    fun p => (nbNode u v a b (eqP.symm p)).map eqP.toEmbedding
  have hmem (p q : Node n k × Bool) :
      eqP q ∈ nb (eqP p) ↔ q ∈ nbNode u v a b p := by
    simp [nb]
  refine ⟨m, slot, read, nb, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i e h
    have hp : Node.base i = Node.arcSlot e := eqN.injective h
    cases hp
  · intro p
    obtain ⟨q, rfl⟩ := eqP.surjective p
    refine ⟨fun h => nbNode_not_mem_self u v a b q ((hmem _ _).mp h), ?_⟩
    simpa [nb] using nbNode_card_le u v a b q
  · intro p q
    obtain ⟨p', rfl⟩ := eqP.surjective p
    obtain ⟨q', rfl⟩ := eqP.surjective q
    rw [hmem, hmem]
    exact nbNode_symm u v a b p' q'
  · intro i
    obtain ⟨p, rfl⟩ := eqN.surjective i
    exact (hmem (p,false) (p,true)).mpr (by simp [nb_parts])
  · intro c i j hij
    obtain ⟨p, rfl⟩ := eqN.surjective i
    obtain ⟨q, rfl⟩ := eqN.surjective j
    have h := (hmem (p,c) (q,c)).mp hij
    rcases nbNode_same u v a b p q c h with ⟨e, ha, hb, hp | hq⟩
    · exact ⟨e, ha, hb, Or.inl (congrArg eqN hp)⟩
    · exact ⟨e, ha, hb, Or.inr (congrArg eqN hq)⟩
  · intro z
    dsimp only
    let phys (x : Fin m × Bool → Bool) : Prop :=
      (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
      (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
      (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
    have hphys (x : Fin m × Bool → Bool) :
        phys x ↔ Valid u v a b z (x ∘ eqP) := by
      constructor
      · rintro ⟨hc, hs, hn⟩
        refine ⟨fun p q h => hc _ _ ((hmem _ _).mpr h), hs, ?_⟩
        intro p hp
        exact hn (eqN p) (fun e he => hp e (eqN.injective he))
      · rintro ⟨hc, hs, hn⟩
        refine ⟨?_, hs, ?_⟩
        · intro p q h
          obtain ⟨p', rfl⟩ := eqP.surjective p
          obtain ⟨q', rfl⟩ := eqP.surjective q
          exact hc p' q' ((hmem _ _).mp h)
        · intro i hi
          obtain ⟨p, rfl⟩ := eqN.surjective i
          exact hn p (fun e he => hi e (congrArg eqN he))
    constructor
    · intro x hx
      exact (recover_valid u v a b z (x ∘ eqP) ((hphys x).mp hx)).1
    · intro y hy
      let xN := liftValues u v z y
      let x : Fin m × Bool → Bool := xN ∘ eqP.symm
      have hcomp : x ∘ eqP = xN := by
        funext p
        simp [x, Function.comp_def]
      have hx : phys x := (hphys x).mpr (hcomp.symm ▸ liftValid u v a b z y hy)
      have hd : readValues (x ∘ eqP) = y := by
        rw [hcomp]
        funext i
        simp [xN, readValues, liftValues]
      refine ⟨x, ⟨hx, hd⟩, ?_⟩
      intro x' hx'
      have hdecoded : readValues (x' ∘ eqP) = y := hx'.2
      have hrec := (recover_valid u v a b z (x' ∘ eqP) ((hphys x').mp hx'.1)).2
      rw [hdecoded] at hrec
      funext p
      obtain ⟨q, rfl⟩ := eqP.surjective p
      change (x' ∘ eqP) q = (x ∘ eqP) q
      rw [hrec, hcomp]
