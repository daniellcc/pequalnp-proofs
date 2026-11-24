import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def x1fn (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
    fun i => decide (i = 6)

def x2fn (b : Bool) (x : Fin 8 → Bool) : List Bool :=
  [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]

inductive SymVal where
  | cFalse
  | cTrue
  | wire (k : ℕ)

def SymVal.eval (v : List Bool) : SymVal → Bool
  | SymVal.cFalse => false
  | SymVal.cTrue => true
  | SymVal.wire k => v.getD k false

def initEnv : List SymVal :=
  [SymVal.wire 1, SymVal.wire 0, SymVal.wire 4, SymVal.wire 7,
   SymVal.wire 5, SymVal.wire 2, SymVal.cFalse, SymVal.wire 6,
   SymVal.wire 3, SymVal.wire 1]

def step (st : List Gate × List SymVal) (g : Gate) : List Gate × List SymVal :=
  let gs := st.1
  let env := st.2
  let nextW := 8 + gs.length
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (gs, env ++ [SymVal.cTrue])
    | a :: _ =>
      match env.getD a SymVal.cFalse with
      | SymVal.cFalse => (gs, env ++ [SymVal.cTrue])
      | SymVal.cTrue => (gs, env ++ [SymVal.cFalse])
      | SymVal.wire k => (gs ++ [⟨GateOp.not, [k]⟩], env ++ [SymVal.wire nextW])
  | GateOp.and =>
    match g.inputs with
    | [] => (gs, env ++ [SymVal.cTrue])
    | [a] => (gs, env ++ [env.getD a SymVal.cFalse])
    | a :: b :: _ =>
      match env.getD a SymVal.cFalse, env.getD b SymVal.cFalse with
      | SymVal.cFalse, _ => (gs, env ++ [SymVal.cFalse])
      | _, SymVal.cFalse => (gs, env ++ [SymVal.cFalse])
      | SymVal.cTrue, vb => (gs, env ++ [vb])
      | va, SymVal.cTrue => (gs, env ++ [va])
      | SymVal.wire k1, SymVal.wire k2 =>
        (gs ++ [⟨GateOp.and, [k1, k2]⟩], env ++ [SymVal.wire nextW])
  | GateOp.or =>
    match g.inputs with
    | [] => (gs, env ++ [SymVal.cFalse])
    | [a] => (gs, env ++ [env.getD a SymVal.cFalse])
    | a :: b :: _ =>
      match env.getD a SymVal.cFalse, env.getD b SymVal.cFalse with
      | SymVal.cTrue, _ => (gs, env ++ [SymVal.cTrue])
      | _, SymVal.cTrue => (gs, env ++ [SymVal.cTrue])
      | SymVal.cFalse, vb => (gs, env ++ [vb])
      | va, SymVal.cFalse => (gs, env ++ [va])
      | SymVal.wire k1, SymVal.wire k2 =>
        (gs ++ [⟨GateOp.or, [k1, k2]⟩], env ++ [SymVal.wire nextW])
  | _ => (gs, env ++ [SymVal.cFalse])

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_right_single {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by simp

lemma SymVal_eval_append_ok (v : List Bool) (g : Gate) (sv : SymVal)
    (h : match sv with | SymVal.wire k => k < v.length | _ => True) :
    sv.eval (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) = sv.eval v := by
  cases sv with
  | cFalse => rfl
  | cTrue => rfl
  | wire k =>
    simp only [SymVal.eval]
    rw [List.getD_append _ _ _ _ h]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def StateInv (st : List Gate × List SymVal) : Prop :=
  (∀ g ∈ st.1, GateOK g) ∧
  10 ≤ st.2.length ∧
  st.2.getD 6 SymVal.cFalse = SymVal.cFalse ∧
  (∀ sv ∈ st.2, match sv with | SymVal.wire k => k < 8 + st.1.length | _ => True)

lemma initEnv_inv : StateInv ([], initEnv) := by
  refine ⟨fun g hg => by simp at hg, by simp [initEnv], by simp [initEnv], ?_⟩
  intro sv hsv
  simp only [initEnv, List.mem_cons, List.not_mem_nil, or_false] at hsv
  rcases hsv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma step_inv (st : List Gate × List SymVal) (g : Gate) (hst : StateInv st) (hg : GateOK g) :
    StateInv (step st g) ∧
    (step st g).2.length = st.2.length + 1 ∧
    (x1fn g = true → (step st g).1.length = st.1.length) ∧
    (step st g).1.length ≤ st.1.length + 1 := by
  rcases hst with ⟨hfan, hlen, h6, hwires⟩
  rcases hg with ⟨hop, hinlen⟩
  have hmem : ∀ w, (st.2.getD w SymVal.cFalse) = SymVal.cFalse ∨
      st.2.getD w SymVal.cFalse ∈ st.2 := by
    intro w
    by_cases hw : w < st.2.length
    · rw [List.getD_eq_getElem _ _ hw]
      exact Or.inr (List.getElem_mem hw)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Or.inl rfl
  have hget : ∀ w, match st.2.getD w SymVal.cFalse with
      | SymVal.wire k => k < 8 + st.1.length
      | _ => True := by
    intro w
    rcases hmem w with heq | hm
    · rw [heq]; trivial
    · exact hwires _ hm
  have hx1_and_or : ∀ a b : ℕ, x1fn ⟨g.op, [a, b]⟩ = true →
      g.op = GateOp.and ∨ g.op = GateOp.or → a = 6 ∨ b = 6 := by
    intro a b hx hop2
    simp only [x1fn] at hx
    rcases hop2 with h | h <;> simp [h, GateOp.eval] at hx
    · exact hx
    · exact hx
  have hx1_single : ∀ a : ℕ, x1fn ⟨g.op, [a]⟩ = true → a = 6 := by
    intro a hx
    simp only [x1fn] at hx
    rcases hop with h | h | h <;> simp [h, GateOp.eval] at hx <;> exact hx
  have hx1_nil : x1fn ⟨g.op, []⟩ = true → False := by
    intro hx
    simp only [x1fn] at hx
    rcases hop with h | h | h <;> simp [h, GateOp.eval] at hx
  have hx1_not : ∀ a b : ℕ, x1fn ⟨GateOp.not, [a, b]⟩ = true → a = 6 := by
    intro a b hx
    simp [x1fn, GateOp.eval] at hx
    exact hx
  rcases hop with hop_and | hop_or | hop_not
  · cases h_op : g.op with
    | and =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
        · rw [List.getD_append st.2 _ SymVal.cFalse 6 (by omega)]; exact h6
        · intro sv hsv
          simp only [List.mem_append, List.mem_singleton] at hsv
          rcases hsv with hsv | rfl
          · exact hwires sv hsv
          · trivial
        · exfalso; exact hx1_nil (by cases g; simp_all)
      | cons a t =>
        cases t with
        | nil =>
          simp only [step, h_op, h_in]
          refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun _ => by simp, by simp⟩
          · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
          · intro sv hsv
            simp only [List.mem_append, List.mem_singleton] at hsv
            rcases hsv with hsv | rfl
            · exact hwires sv hsv
            · exact hget a
        | cons b t' =>
          cases t' with
          | nil =>
            simp only [step, h_op, h_in]
            have h6a : a = 6 → st.2.getD a SymVal.cFalse = SymVal.cFalse := fun h => h ▸ h6
            have h6b : b = 6 → st.2.getD b SymVal.cFalse = SymVal.cFalse := fun h => h ▸ h6
            cases ha : st.2.getD a SymVal.cFalse <;> cases hb : st.2.getD b SymVal.cFalse <;>
              simp only []
            all_goals try (
              refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun _ => by simp, by simp⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
              · intro sv hsv
                simp only [List.mem_append, List.mem_singleton] at hsv
                rcases hsv with hsv | rfl
                · exact hwires sv hsv
                · first | trivial | (have := hget a; rw [ha] at this; exact this) | (have := hget b; rw [hb] at this; exact this))
            · refine ⟨⟨?_, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
              · intro g' hg'
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
                rcases hg' with hg' | rfl
                · exact hfan g' hg'
                · exact ⟨by simp, by simp⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
              · intro sv hsv
                simp only [List.mem_append, List.mem_singleton] at hsv
                rcases hsv with hsv | rfl
                · have := hwires sv hsv
                  cases sv with | cFalse => trivial | cTrue => trivial | wire k => simp at this ⊢
                · simp; omega
              · exfalso
                have hab : a = 6 ∨ b = 6 := hx1_and_or a b (by cases g; simp_all) (Or.inl h_op)
                rcases hab with rfl | rfl
                · rw [h6] at ha; cases ha
                · rw [h6] at hb; cases hb
          | cons c t'' =>
            simp [h_in] at hinlen
    | or => simp [h_op] at hop_and
    | not => simp [h_op] at hop_and
    | mod m => simp [h_op] at hop_and
    | maj => simp [h_op] at hop_and
  · cases h_op : g.op with
    | or =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
        · rw [List.getD_append st.2 _ SymVal.cFalse 6 (by omega)]; exact h6
        · intro sv hsv
          simp only [List.mem_append, List.mem_singleton] at hsv
          rcases hsv with hsv | rfl
          · exact hwires sv hsv
          · trivial
        · exfalso; exact hx1_nil (by cases g; simp_all)
      | cons a t =>
        cases t with
        | nil =>
          simp only [step, h_op, h_in]
          refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun _ => by simp, by simp⟩
          · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
          · intro sv hsv
            simp only [List.mem_append, List.mem_singleton] at hsv
            rcases hsv with hsv | rfl
            · exact hwires sv hsv
            · exact hget a
        | cons b t' =>
          cases t' with
          | nil =>
            simp only [step, h_op, h_in]
            cases ha : st.2.getD a SymVal.cFalse <;> cases hb : st.2.getD b SymVal.cFalse <;>
              simp only []
            all_goals try (
              refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun _ => by simp, by simp⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
              · intro sv hsv
                simp only [List.mem_append, List.mem_singleton] at hsv
                rcases hsv with hsv | rfl
                · exact hwires sv hsv
                · first | trivial | (have := hget a; rw [ha] at this; exact this) | (have := hget b; rw [hb] at this; exact this))
            · refine ⟨⟨?_, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
              · intro g' hg'
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
                rcases hg' with hg' | rfl
                · exact hfan g' hg'
                · exact ⟨by simp, by simp⟩
              · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
              · intro sv hsv
                simp only [List.mem_append, List.mem_singleton] at hsv
                rcases hsv with hsv | rfl
                · have := hwires sv hsv
                  cases sv with | cFalse => trivial | cTrue => trivial | wire k => simp at this ⊢
                · simp; omega
              · exfalso
                have hab : a = 6 ∨ b = 6 := hx1_and_or a b (by cases g; simp_all) (Or.inr h_op)
                rcases hab with rfl | rfl
                · rw [h6] at ha; cases ha
                · rw [h6] at hb; cases hb
          | cons c t'' =>
            simp [h_in] at hinlen
    | and => simp [h_op] at hop_or
    | not => simp [h_op] at hop_or
    | mod m => simp [h_op] at hop_or
    | maj => simp [h_op] at hop_or
  · rw [Set.mem_singleton_iff] at hop_not
    cases h_op : g.op with
    | not =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
        · rw [List.getD_append st.2 _ SymVal.cFalse 6 (by omega)]; exact h6
        · intro sv hsv
          simp only [List.mem_append, List.mem_singleton] at hsv
          rcases hsv with hsv | rfl
          · exact hwires sv hsv
          · trivial
        · exfalso; exact hx1_nil (by cases g; simp_all)
      | cons a t =>
        simp only [step, h_op, h_in]
        cases ha : st.2.getD a SymVal.cFalse <;> simp only []
        all_goals try (
          refine ⟨⟨hfan, by simp; omega, ?_, ?_⟩, by simp, fun _ => by simp, by simp⟩
          · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
          · intro sv hsv
            simp only [List.mem_append, List.mem_singleton] at hsv
            rcases hsv with hsv | rfl
            · exact hwires sv hsv
            · trivial)
        · refine ⟨⟨?_, by simp; omega, ?_, ?_⟩, by simp, fun hx => ?_, by simp⟩
          · intro g' hg'
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with hg' | rfl
            · exact hfan g' hg'
            · exact ⟨by simp, by simp⟩
          · rw [List.getD_append _ _ _ _ (by omega)]; exact h6
          · intro sv hsv
            simp only [List.mem_append, List.mem_singleton] at hsv
            rcases hsv with hsv | rfl
            · have := hwires sv hsv
              cases sv with | cFalse => trivial | cTrue => trivial | wire k => simp at this ⊢
            · simp; omega
          · exfalso
            cases t with
            | nil =>
              have := hx1_single a (by cases g; simp_all)
              subst this; rw [h6] at ha; cases ha
            | cons b t' =>
              cases t' with
              | nil =>
                have := hx1_not a b (by cases g; simp_all)
                subst this; rw [h6] at ha; cases ha
              | cons c t'' =>
                simp [h_in] at hinlen
    | and => simp [h_op] at hop_not
    | or => simp [h_op] at hop_not
    | mod m => simp [h_op] at hop_not
    | maj => simp [h_op] at hop_not

lemma step_eval (st : List Gate × List SymVal) (g : Gate) (x : Fin 8 → Bool) (w0 : List Bool)
    (hst : StateInv st) (hg : GateOK g) (hw0 : w0.length = st.2.length)
    (heval : ∀ i, (st.2.getD i SymVal.cFalse).eval (wiresFrom st.1 (List.ofFn x)) = w0.getD i false) :
    ∀ i, ((step st g).2.getD i SymVal.cFalse).eval (wiresFrom (step st g).1 (List.ofFn x)) =
      (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).getD i false := by
  intro i
  rcases hst with ⟨_, hlen, _, hwires⟩
  rcases hg with ⟨hop, hinlen⟩
  have hmem : ∀ w, st.2.getD w SymVal.cFalse = SymVal.cFalse ∨ st.2.getD w SymVal.cFalse ∈ st.2 := by
    intro w
    by_cases hw : w < st.2.length
    · rw [List.getD_eq_getElem _ _ hw]; exact Or.inr (List.getElem_mem hw)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl
  have hget_ok : ∀ w, match st.2.getD w SymVal.cFalse with
      | SymVal.wire k => k < (wiresFrom st.1 (List.ofFn x)).length
      | _ => True := by
    intro w
    rw [wiresFrom_length, List.length_ofFn]
    rcases hmem w with heq | hm
    · rw [heq]; trivial
    · exact hwires _ hm
  have hcommon : ∀ (gs' : List Gate) (sv_new : SymVal),
      (sv_new.eval (wiresFrom gs' (List.ofFn x)) =
        g.op.eval (g.inputs.map fun j => w0.getD j false)) →
      (gs' = st.1 ∨ ∃ g', gs' = st.1 ++ [g']) →
      ((st.2 ++ [sv_new]).getD i SymVal.cFalse).eval (wiresFrom gs' (List.ofFn x)) =
        (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).getD i false := by
    intro gs' sv_new hsv hgs
    by_cases hi : i < st.2.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
      rcases hgs with rfl | ⟨g', rfl⟩
      · exact heval i
      · rw [wiresFrom_append, wiresFrom, List.foldl_cons, List.foldl_nil]
        rw [SymVal_eval_append_ok _ g' _ (hget_ok i)]
        exact heval i
    · by_cases hieq : i = st.2.length
      · subst hieq
        have hw0' : st.2.length = w0.length := hw0.symm
        rw [getD_append_right_single]
        conv_rhs => rw [hw0', getD_append_right_single]
        exact hsv
      · have h1 : st.2.length < i := by omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        rfl
  rcases hop with hop_and | hop_or | hop_not
  · cases h_op : g.op with
    | and =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        rw [h_op, h_in] at hcommon
        exact hcommon st.1 SymVal.cTrue (by simp [GateOp.eval, SymVal.eval]) (Or.inl rfl)
      | cons a t =>
        cases t with
        | nil =>
          simp only [step, h_op, h_in]
          rw [h_op, h_in] at hcommon
          exact hcommon st.1 (st.2.getD a SymVal.cFalse)
            (by simp [GateOp.eval, SymVal.eval, heval a]) (Or.inl rfl)
        | cons b t' =>
          cases t' with
          | nil =>
            simp only [step, h_op, h_in]
            rw [h_op, h_in] at hcommon
            have hae := heval a
            have hbe := heval b
            cases ha : st.2.getD a SymVal.cFalse <;> cases hb : st.2.getD b SymVal.cFalse <;>
              simp only []
            all_goals try (
              refine hcommon st.1 _ ?_ (Or.inl rfl)
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [← hae, ← hbe, ha, hb]
              rfl)
            · refine hcommon (st.1 ++ [⟨GateOp.and, [_, _]⟩]) _ ?_ (Or.inr ⟨_, rfl⟩)
              rw [wiresFrom_append, wiresFrom, List.foldl_cons, List.foldl_nil]
              simp only [SymVal.eval]
              have hlen_w : (wiresFrom st.1 (List.ofFn x)).length = 8 + st.1.length := by
                rw [wiresFrom_length, List.length_ofFn]; omega
              rw [← hlen_w, getD_append_right_single]
              simp only [GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [← hae, ← hbe, ha, hb]
              rfl
          | cons c t'' => simp [h_in] at hinlen
    | or => simp [h_op] at hop_and
    | not => simp [h_op] at hop_and
    | mod m => simp [h_op] at hop_and
    | maj => simp [h_op] at hop_and
  · cases h_op : g.op with
    | or =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        rw [h_op, h_in] at hcommon
        exact hcommon st.1 SymVal.cFalse (by simp [GateOp.eval, SymVal.eval]) (Or.inl rfl)
      | cons a t =>
        cases t with
        | nil =>
          simp only [step, h_op, h_in]
          rw [h_op, h_in] at hcommon
          exact hcommon st.1 (st.2.getD a SymVal.cFalse)
            (by simp [GateOp.eval, SymVal.eval, heval a]) (Or.inl rfl)
        | cons b t' =>
          cases t' with
          | nil =>
            simp only [step, h_op, h_in]
            rw [h_op, h_in] at hcommon
            have hae := heval a
            have hbe := heval b
            cases ha : st.2.getD a SymVal.cFalse <;> cases hb : st.2.getD b SymVal.cFalse <;>
              simp only []
            all_goals try (
              refine hcommon st.1 _ ?_ (Or.inl rfl)
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [← hae, ← hbe, ha, hb]
              rfl)
            · refine hcommon (st.1 ++ [⟨GateOp.or, [_, _]⟩]) _ ?_ (Or.inr ⟨_, rfl⟩)
              rw [wiresFrom_append, wiresFrom, List.foldl_cons, List.foldl_nil]
              simp only [SymVal.eval]
              have hlen_w : (wiresFrom st.1 (List.ofFn x)).length = 8 + st.1.length := by
                rw [wiresFrom_length, List.length_ofFn]; omega
              rw [← hlen_w, getD_append_right_single]
              simp only [GateOp.eval, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [← hae, ← hbe, ha, hb]
              rfl
          | cons c t'' => simp [h_in] at hinlen
    | and => simp [h_op] at hop_or
    | not => simp [h_op] at hop_or
    | mod m => simp [h_op] at hop_or
    | maj => simp [h_op] at hop_or
  · cases h_op : g.op with
    | not =>
      cases h_in : g.inputs with
      | nil =>
        simp only [step, h_op, h_in]
        rw [h_op, h_in] at hcommon
        exact hcommon st.1 SymVal.cTrue (by simp [GateOp.eval, SymVal.eval, h_op, h_in]) (Or.inl rfl)
      | cons a t =>
        simp only [step, h_op, h_in]
        rw [h_op, h_in] at hcommon
        have hae := heval a
        cases ha : st.2.getD a SymVal.cFalse <;> simp only []
        all_goals try (
          refine hcommon st.1 _ ?_ (Or.inl rfl)
          simp only [GateOp.eval, List.map_cons, List.headD_cons]
          rw [← hae, ha]
          rfl)
        · refine hcommon (st.1 ++ [⟨GateOp.not, [_]⟩]) _ ?_ (Or.inr ⟨_, rfl⟩)
          rw [wiresFrom_append, wiresFrom, List.foldl_cons, List.foldl_nil]
          simp only [SymVal.eval]
          have hlen_w : (wiresFrom st.1 (List.ofFn x)).length = 8 + st.1.length := by
            rw [wiresFrom_length, List.length_ofFn]; omega
          rw [← hlen_w, getD_append_right_single]
          dsimp only [GateOp.eval, List.map_cons, List.headD_cons]
          rw [← hae, ha]
          rfl
    | and => simp [h_op] at hop_not
    | or => simp [h_op] at hop_not
    | mod m => simp [h_op] at hop_not
    | maj => simp [h_op] at hop_not

lemma foldl_spec (gs : List Gate) :
    ∀ (st : List Gate × List SymVal), StateInv st →
    (∀ g ∈ gs, GateOK g) →
    let stf := gs.foldl step st
    StateInv stf ∧
    stf.2.length = st.2.length + gs.length ∧
    stf.1.length + List.countP x1fn gs ≤ st.1.length + gs.length ∧
    (∀ (x : Fin 8 → Bool) (w0 : List Bool), w0.length = st.2.length →
      (∀ i, (st.2.getD i SymVal.cFalse).eval (wiresFrom st.1 (List.ofFn x)) = w0.getD i false) →
      ∀ i, (stf.2.getD i SymVal.cFalse).eval (wiresFrom stf.1 (List.ofFn x)) = (wiresFrom gs w0).getD i false) := by
  induction gs with
  | nil =>
    intro st hst _
    exact ⟨hst, rfl, by simp, fun x w0 _ hev i => by simpa [wiresFrom] using hev i⟩
  | cons g gs ih =>
    intro st hst hgs
    have hg : GateOK g := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, GateOK g' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have h1 := step_inv st g hst hg
    have h2 := ih (step st g) h1.1 hgs'
    refine ⟨h2.1, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, List.length_cons]
      rw [h2.2.1, h1.2.1]
      omega
    · simp only [List.foldl_cons, List.countP_cons, List.length_cons]
      by_cases hx1 : x1fn g = true
      · simp only [hx1, ↓reduceIte]
        have := h1.2.2.1 hx1
        omega
      · simp only [Bool.not_eq_true] at hx1
        simp only [hx1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have := h1.2.2.2
        have h2' := h2.2.2.1
        omega
    · intro x w0 hw0 hev i
      simp only [List.foldl_cons, wiresFrom]
      have hs1 := step_eval st g x w0 hst hg hw0 hev
      have hw1 : (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).length = (step st g).2.length := by
        simp [hw0, h1.2.1]
      exact h2.2.2.2 x _ hw1 hs1 i

lemma main (x3 : Circuit) (hfan : FanInTwo x3) (hcnt : 2 ≤ List.countP x1fn x3.gates)
    (hfalse : ∃ x6 : Fin 8 → Bool, x3.eval (x2fn false x6) = false) :
    ∃ x7 : Circuit, FanInTwo x7 ∧ x7.size + 2 ≤ x3.size ∧
      ∀ x8 : Fin 8 → Bool, x7.eval (List.ofFn x8) = x3.eval (x2fn false x8) := by
  have hgs : ∀ g ∈ x3.gates, GateOK g := fun g hg => hfan g hg
  have hspec := foldl_spec x3.gates ([], initEnv) initEnv_inv hgs
  let stf := x3.gates.foldl step ([], initEnv)
  have hinit_eval : ∀ (x : Fin 8 → Bool) i,
      (initEnv.getD i SymVal.cFalse).eval (wiresFrom [] (List.ofFn x)) = (x2fn false x).getD i false := by
    intro x i
    rcases lt_trichotomy i 10 with hi | hi | hi
    · interval_cases i <;> simp [initEnv, x2fn, SymVal.eval, wiresFrom]
    · subst hi; simp [initEnv, x2fn, SymVal.eval, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [initEnv]; omega),
        List.getD_eq_default _ _ (by simp [x2fn]; omega)]
      rfl
  have hev : ∀ x : Fin 8 → Bool,
      (stf.2.getD x3.output SymVal.cFalse).eval (wiresFrom stf.1 (List.ofFn x)) = x3.eval (x2fn false x) := by
    intro x
    have := hspec.2.2.2 x (x2fn false x) (by simp [initEnv, x2fn]) (hinit_eval x) x3.output
    simpa [Circuit.eval, Circuit.wires, wiresFrom] using this
  have hsz : stf.1.length + 2 ≤ x3.size := by
    have := hspec.2.2.1
    dsimp only [stf]
    simp only [List.length_nil, Nat.zero_add, Circuit.size] at this ⊢
    omega
  cases hout : stf.2.getD x3.output SymVal.cFalse with
  | cFalse =>
    refine ⟨⟨[], 8⟩, fun g hg => by simp at hg, ?_, fun x => ?_⟩
    · simp only [Circuit.size, List.length_nil, Nat.zero_add]
      have : x3.gates.countP x1fn ≤ x3.gates.length := List.countP_le_length
      change 2 ≤ x3.gates.length
      omega
    · rw [← hev x, hout]
      simp [Circuit.eval, Circuit.wires, SymVal.eval]
  | cTrue =>
    exfalso
    rcases hfalse with ⟨x6, hx6⟩
    have := hev x6
    rw [hout, hx6] at this
    simp [SymVal.eval] at this
  | wire k =>
    refine ⟨⟨stf.1, k⟩, fun g hg => hspec.1.1 g hg, hsz, fun x => ?_⟩
    rw [← hev x, hout]
    simp [Circuit.eval, Circuit.wires, wiresFrom, SymVal.eval]

end PEqualNP.Outside.L_meta_2502

theorem PEqualNP.Outside.L_meta_2502 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (2 : ℕ) ≤ List.countP x1 x3.gates → (∃ (x6 : Fin (8 : ℕ) → Bool), x3.eval (x2 Bool.false x6) = Bool.false) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x8 : Fin (8 : ℕ) → Bool), x7.eval (List.ofFn x8) = x3.eval (x2 Bool.false x8) :=
  fun x3 hfan hcnt hfalse => PEqualNP.Outside.L_meta_2502.main x3 hfan hcnt hfalse
