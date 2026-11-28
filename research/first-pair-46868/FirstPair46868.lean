import PEqualNP.Defs

namespace PEqualNP.Outside.FirstPair46868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 6) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 6) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 6) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 6) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

def Prog : Set F → F → ℕ → Prop
  | s, f, 0 => Av s f
  | s, f, k + 1 => ∃ (t : Bool) (a b : F), Av s a ∧ Av s b ∧ Prog (insert (comb t a b) s) f k

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction k generalizing s f with
  | zero => exact fun t hs => ⟨0, le_rfl, av_rs hs p, fun _ h' => smp_av h' p⟩
  | succ k ih =>
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih tail t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih tail (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, ⟨tag, rs i c a, rs i c b, pa, pb, q⟩, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 6} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 6} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction k generalizing s f with
  | zero => exact absurd (li_smp (li_av hs p)) (hf true)
  | succ k ih =>
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih tail (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, ⟨tag, rs i c a, rs i c b, av_rs ht ha, av_rs ht hb, q⟩⟩

def stock : Set F := Set.range fun (i : Fin 6) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

-- If no step can be saved by pinning an input, agreement of the initial
-- wires, apart from wires made constant by that pin, propagates to the output.
theorem av_agrees_or_pinned {s : Set F} {i : Fin 6} {c : Bool} {x y : X} {f : F}
    (hs : ∀ u ∈ s, u x = u y ∨ Cst (rs i c u)) (hf : Av s f) :
    f x = f y ∨ Cst (rs i c f) := by
  rcases hf with ⟨b, rfl⟩ | ⟨u, hu, h | h⟩
  · exact Or.inl rfl
  · rw [h]
    exact hs u hu
  · rw [h]
    rcases hs u hu with h' | ⟨b, h'⟩
    · exact Or.inl (congrArg not h')
    · exact Or.inr ⟨!b, by funext v; exact congrArg not (congrFun h' v)⟩

theorem restrict_agreement {i : Fin 6} {c : Bool} {s : Set F} {f : F} {k : Nat}
    (p : Prog s f k) (x y : X) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
      ∃ j ≤ k, Prog t (rs i c f) j ∧
        (j = k → (∀ u ∈ s, u x = u y ∨ Cst (rs i c u)) → f x = f y ∨ Cst (rs i c f)) := by
  induction k generalizing s f with
  | zero =>
    intro t hs
    exact ⟨0, le_rfl, av_rs hs p, fun _ hag => av_agrees_or_pinned hag p⟩
  | succ k ih =>
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := restrict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs u hu)
      exact ⟨j, by omega, q, fun h => by omega⟩
    · obtain ⟨j, hj, q, Hag⟩ := ih tail
        (insert (comb tag (rs i c a) (rs i c b)) t) (by
          intro u hu
          rcases Set.mem_insert_iff.mp hu with rfl | hu
          · exact av_mem (Set.mem_insert _ _)
          · exact av_ins _ (hs u hu))
      refine ⟨j + 1, by omega, ⟨tag, rs i c a, rs i c b, pa, pb, q⟩, ?_⟩
      intro hjk h
      apply Hag (by omega)
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have ea := (av_agrees_or_pinned h ha).resolve_right (fun h' => hc (.inl h'))
        have eb := (av_agrees_or_pinned h hb).resolve_right (fun h' => hc (.inr h'))
        exact Or.inl (by simp only [comb, ea, eb])
      · exact h _ hu

theorem rest_agrees {n k : Nat} {f g : F} {i : Fin 6} {c : Bool} {x y : X}
    (tail : Prog (insert g stock) f k) (bound : Low n (rs i c f)) (hk : k ≤ n)
    (hpin : Av stock (rs i c g)) (hnonc : ¬ Cst (rs i c f))
    (hxy : ∀ r, r ≠ i → x r = y r) (hg : g x = g y) : f x = f y := by
  obtain ⟨j, hj, p, ag⟩ := restrict_agreement tail x y stock (by
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact hpin
    · exact stock_rs i c u hu)
  have hl := bound j p
  refine (ag (by omega) ?_).resolve_right hnonc
  intro u hu
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · exact Or.inl hg
  · obtain ⟨r, rfl⟩ := hu
    by_cases hr : r = i
    · subst r
      exact Or.inr ⟨c, by funext v; simp [rs]⟩
    · exact Or.inl (hxy r hr)

def EssentialAfter (f : F) (i j : Fin 6) : Prop :=
  ∀ d : Bool, ∃ x y : X, x j = d ∧ y j = d ∧
    (∀ r, r ≠ i → x r = y r) ∧ f x ≠ f y

def Literal (i : Fin 6) (phase : Bool) : F := fun x => xor (x i) phase

theorem literal_av (i : Fin 6) (phase : Bool) : Av stock (Literal i phase) := by
  cases phase
  · exact Or.inr ⟨fun x => x i, ⟨i, rfl⟩, Or.inl (by funext x; simp [Literal])⟩
  · exact Or.inr ⟨fun x => x i, ⟨i, rfl⟩, Or.inr (by funext x; simp [Literal])⟩

theorem av_stock_shape {f : F} (h : Av stock f) : Cst f ∨ ∃ i e, f = Literal i e := by
  rcases h with hc | ⟨u, ⟨i, rfl⟩, rfl | rfl⟩
  · exact Or.inl hc
  · exact Or.inr ⟨i, false, by funext x; simp [Literal]⟩
  · exact Or.inr ⟨i, true, by funext x; simp [Literal]⟩

theorem unary_av (i : Fin 6) (g : Bool → Bool) : Av stock (fun x => g (x i)) := by
  cases hf : g false <;> cases ht : g true
  · exact Or.inl ⟨false, by funext x; cases h : x i <;> simp [hf, ht]⟩
  · have h : (fun x : X => g (x i)) = Literal i false := by
      funext x
      cases hx : x i <;> simp [Literal, hx, hf, ht]
    rw [h]
    exact literal_av i false
  · have h : (fun x : X => g (x i)) = Literal i true := by
      funext x
      cases hx : x i <;> simp [Literal, hx, hf, ht]
    rw [h]
    exact literal_av i true
  · exact Or.inl ⟨true, by funext x; cases h : x i <;> simp [hf, ht]⟩

theorem comb_swap (tag : Bool) (a b : F) : comb tag a b = comb tag b a := by
  funext x
  cases tag <;> simp [comb, Bool.and_comm, Bool.or_comm]

theorem prog_covered {s : Set F} {k : Nat} {f : F} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t u) → Prog t f k := by
  have forward {r t : Set F} (h : ∀ u ∈ r, Av t u) {v} (hv : Av r v) : Av t v := by
    rcases hv with hc | ⟨u, hu, rfl | rfl⟩
    · exact Or.inl hc
    · exact h _ hu
    · exact av_not (h _ hu)
  induction k generalizing s f with
  | zero => exact fun t h => forward h p
  | succ k ih =>
    intro t h
    rcases p with ⟨tag, a, b, ha, hb, tail⟩
    refine ⟨tag, a, b, forward h ha, forward h hb, ih tail _ ?_⟩
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact av_mem (Set.mem_insert _ _)
    · exact av_ins _ (h _ hu)

theorem first_literal_excluded {f : F} {n k : Nat} {i j : Fin 6} {tag ai aj : Bool}
    (hf : EssentialAfter f i j) (high : ∃ c, Low n (rs i c f) ∧ ¬ Cst (rs i c f))
    (hk : k ≤ n) :
    ¬ Prog (insert (comb tag (Literal i ai) (Literal j aj)) stock) f k := by
  intro tail
  obtain ⟨c, hbound, hnc⟩ := high
  obtain ⟨x, y, hx, hy, hxy, hne⟩ := hf (xor (!tag) aj)
  have hpin : Av stock (rs i c (comb tag (Literal i ai) (Literal j aj))) := by
    have hl : Cst (rs i c (Literal i ai)) := ⟨xor c ai, by funext v; simp [Literal, rs]⟩
    exact av_cheap tag (av_rs (stock_rs i c) (literal_av i ai))
      (av_rs (stock_rs i c) (literal_av j aj)) (Or.inl hl)
  have hg : comb tag (Literal i ai) (Literal j aj) x =
      comb tag (Literal i ai) (Literal j aj) y := by
    cases tag <;> cases aj <;> simp [comb, Literal, hx, hy]
  exact hne (rest_agrees tail hbound hk hpin hnc hxy hg)

theorem lower_first_pair {f : F} {n : Nat} (hbase : Low (n + 1) f)
    (hcover : ∀ i j : Fin 6, i ≠ j →
      (EssentialAfter f i j ∧ ∃ c, Low n (rs i c f) ∧ ¬ Cst (rs i c f)) ∨
      (EssentialAfter f j i ∧ ∃ c, Low n (rs j c f) ∧ ¬ Cst (rs j c f))) : Low (n + 2) f := by
  intro k p
  by_contra h
  have hl := hbase k p
  have hk : k = n + 1 := by omega
  subst k
  rcases p with ⟨tag, a, b, ha, hb, tail⟩
  have expensive : ¬ Av stock (comb tag a b) := by
    intro hc
    have shorter : Prog stock f n := prog_covered tail stock (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact hc
      · exact av_mem hu)
    have := hbase n shorter
    omega
  rcases av_stock_shape ha with hc | ⟨i, ai, rfl⟩
  · exact expensive (av_cheap tag ha hb (.inl hc))
  rcases av_stock_shape hb with hc | ⟨j, aj, rfl⟩
  · exact expensive (av_cheap tag ha hb (.inr hc))
  by_cases hij : i = j
  · subst j
    exact expensive (unary_av i (fun z => if tag then xor z ai && xor z aj else xor z ai || xor z aj))
  rcases hcover i j hij with ⟨hij', high⟩ | ⟨hji', high⟩
  · exact first_literal_excluded hij' high le_rfl tail
  · rw [comb_swap] at tail
    exact first_literal_excluded hji' high le_rfl tail

def renameInput (e : Fin 6 ≃ Fin 6) (f : F) : F := fun x => f (x ∘ e)

theorem av_renamed (e : Fin 6 ≃ Fin 6) {s : Set F} {f : F} (h : Av s f) :
    Av (renameInput e '' s) (renameInput e f) := by
  rcases h with ⟨v, rfl⟩ | ⟨u, hu, eq | eq⟩
  · exact Or.inl ⟨v, rfl⟩
  · rw [eq]
    exact av_mem ⟨u, hu, rfl⟩
  · rw [eq]
    exact av_not (av_mem ⟨u, hu, rfl⟩ : Av (renameInput e '' s) (renameInput e u))

theorem prog_renamed (e : Fin 6 ≃ Fin 6) {s : Set F} {f : F} {k : Nat}
    (p : Prog s f k) : Prog (renameInput e '' s) (renameInput e f) k := by
  induction k generalizing s f with
  | zero => exact av_renamed e p
  | succ k ih =>
    rcases p with ⟨tag,a,b,ha,hb,tail⟩
    have q := ih tail
    rw [Set.image_insert_eq] at q
    exact ⟨tag,renameInput e a,renameInput e b,av_renamed e ha,av_renamed e hb,q⟩

theorem rename_stock (e : Fin 6 ≃ Fin 6) : renameInput e '' stock = stock := by
  ext f
  constructor
  · rintro ⟨u, ⟨i,rfl⟩, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨fun x => x (e.symm i), ⟨e.symm i,rfl⟩, ?_⟩
    funext x
    simp [renameInput]

theorem rename_inverse (e : Fin 6 ≃ Fin 6) (f : F) :
    renameInput e.symm (renameInput e f) = f := by
  funext x
  have h : (x ∘ e.symm) ∘ e = x := by
    funext i
    simp
  exact congrArg f h

theorem lower_renamed (e : Fin 6 ≃ Fin 6) {f : F} {n : Nat} (hl : Low n f) :
    Low n (renameInput e f) := by
  intro k p
  have q := prog_renamed e.symm p
  rw [rename_stock, rename_inverse] at q
  exact hl _ q

theorem positive_lower_nonconstant {f : F} {n : Nat} (h : Low (n+1) f) : ¬ Cst f := by
  intro hc
  have p : Prog stock f 0 := Or.inl hc
  have hp := h _ p
  omega

theorem essential_after_at {f : F} {i j : Fin 6} (hij : i ≠ j) (a b : Nat)
    (ha : (pt a j = false ∧ f (pt a) ≠ f (Function.update (pt a) i (!(pt a i)))) ∧
      (pt b j = true ∧ f (pt b) ≠ f (Function.update (pt b) i (!(pt b i))))) :
    EssentialAfter f i j := by
  have general (d : Bool) (w : Nat) (hw : pt w j = d)
      (hneq : f (pt w) ≠ f (Function.update (pt w) i (!(pt w i)))) :
      ∃ x y : X, x j = d ∧ y j = d ∧ (∀ r, r ≠ i → x r = y r) ∧ f x ≠ f y := by
    refine ⟨pt w, Function.update (pt w) i (!(pt w i)), hw, ?_, ?_, hneq⟩
    · rw [Function.update_of_ne hij.symm, hw]
    · intro r hr
      rw [Function.update_of_ne hr]
  intro d
  cases d
  · exact general false a ha.1.1 ha.1.2
  · exact general true b ha.2.1 ha.2.2


def target : F := fun x => Nat.testBit (4277071594 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower11_of_cofactors (h0 : Low 9 (rs 0 false target))
    (h2 : Low 9 (rs 2 false target)) : Low 11 target := by
  have same3 : renameInput (Equiv.swap (2 : Fin 6) (3 : Fin 6)) (rs 2 false target) = rs 3 false target := by
    apply funext
    decide +kernel
  have h3 : Low 9 (rs 3 false target) := same3 ▸ lower_renamed (Equiv.swap (2 : Fin 6) (3 : Fin 6)) h2
  have same4 : renameInput (Equiv.swap (2 : Fin 6) (4 : Fin 6)) (rs 2 false target) = rs 4 false target := by
    apply funext
    decide +kernel
  have h4 : Low 9 (rs 4 false target) := same4 ▸ lower_renamed (Equiv.swap (2 : Fin 6) (4 : Fin 6)) h2
  have same5 : renameInput (Equiv.swap (2 : Fin 6) (5 : Fin 6)) (rs 2 false target) = rs 5 false target := by
    apply funext
    decide +kernel
  have h5 : Low 9 (rs 5 false target) := same5 ▸ lower_renamed (Equiv.swap (2 : Fin 6) (5 : Fin 6)) h2
  apply lower_first_pair (n := 9)
  · exact one 0 false (good_at 2 60 0 (by decide +kernel)) h0
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact Or.inl ⟨essential_after_at (by decide) 4 2 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 2 4 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 2 8 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 2 16 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 2 32 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact Or.inr ⟨essential_after_at (by decide) 4 2 (by decide +kernel),
      ⟨false, h0, positive_lower_nonconstant h0⟩⟩
  · exact (hij rfl).elim
  · exact Or.inr ⟨essential_after_at (by decide) 1 10 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact Or.inr ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact Or.inr ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact Or.inr ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 10 1 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 10 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact (hij rfl).elim
  · exact Or.inl ⟨essential_after_at (by decide) 1 10 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 18 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 34 (by decide +kernel),
      ⟨false, h2, positive_lower_nonconstant h2⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 6 1 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact (hij rfl).elim
  · exact Or.inl ⟨essential_after_at (by decide) 1 18 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 34 (by decide +kernel),
      ⟨false, h3, positive_lower_nonconstant h3⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 6 1 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 10 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact (hij rfl).elim
  · exact Or.inl ⟨essential_after_at (by decide) 1 34 (by decide +kernel),
      ⟨false, h4, positive_lower_nonconstant h4⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 6 1 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 6 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 10 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact Or.inl ⟨essential_after_at (by decide) 1 18 (by decide +kernel),
      ⟨false, h5, positive_lower_nonconstant h5⟩⟩
  · exact (hij rfl).elim

def witness : Circuit := ⟨[⟨.or, [5, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [4, 3]⟩, ⟨.and, [7, 1]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, witness.eval (List.ofFn x) = target x := by decide +kernel

theorem upper13 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
    ∀ x : X, C.eval (List.ofFn x) = target x :=
  ⟨witness, witness_mono, by decide, witness_eval⟩

end PEqualNP.Outside.FirstPair46868

#print axioms PEqualNP.Outside.FirstPair46868.lower11_of_cofactors
#print axioms PEqualNP.Outside.FirstPair46868.upper13
