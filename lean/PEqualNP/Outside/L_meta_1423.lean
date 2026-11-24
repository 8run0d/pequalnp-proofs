import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1423_aux

-- The live-wire compression argument follows the project proof of L-meta-703.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search n ins = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht n ins nd (lift low run)
  exact Bool.noConfusion (rejection.symm.trans found)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search (m-2) ins = false)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩
def ins_e8a8a888 : List W := [0xf7ffffdffffbffdfdfeffeffffff7ffffbffdefffffefdbffedff7ffff5df7ff30dd002020060030302001e0000f00007801c01e003e00078003c0f03e0c30dd, 0x5d67edbe7def6f7b7f37eff57dbbbbdeddebefeeb9eb6efbb77ddf73d7b75d674d221241c31818c0c1c01e00f0f00787803e01e001c03c781e3c0f01c0334d22, 0xaebc5b73fa5fb2fda9fb7ddaabddd56deeb53d775f35b7d55beaaeee6aebaebc8e3ca48e03e01f00fe00e000ff0007f8003ffe000e003f801fc00ffe00c38e3c, 0xfc838f48bdfc4a8fb7db553eaaee65547a775ba6b67e3661dfbbaa48cfe0fc80fc0c70ffc001fff0000ffff000007ffffc000000fffc0001ffff00000fc0fc0, 0xf81007f910951efefdbed99cccc8f7667739b9dd8db9fbf771b30cc930fff810f000f80fffffe0000000fffffffff800000000000fffffffe000000000fff000]

theorem nd_e8a8a888 : ins_e8a8a888.Nodup := by decide +kernel

theorem spec_e8a8a888 : ∀ j : Fin 512, Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if (ins_e8a8a888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_e8a8a888 : search 6 ins_e8a8a888 = false := by decide +kernel

def gates_e8a8a888 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [9, 11]⟩]

theorem upper_e8a8a888 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8a8a888, 12, ?_, rfl, ?_⟩

  · simp [gates_e8a8a888]

  · decide +kernel

def ins_e8a8c888 : List W := [0xfcdfefdfbff6ff7f7f3ffbf7f77defffaffd7bfef6fbeb7ff6dfd7fb7f5dfcdf3c4d1020600c20c0c1800780001c1e03e00f00780078000f3e03c0f01e0c3c4d, 0x57f7fdbeffdffdedfddfbfddfefeff7ef7bfbfbbefddbdf76f7dff77efb757f741b202418230030306007803c3e0001c00f007800780f8f0003c0f01e03341b2, 0xaf3c5b73f8bf4bf6a7edf76aafb755b77acaf5dd7d66dfaabbeaaeeeb2ebaf3c8e3ca48e03c03c03f8038003fc001fe000fff8003800ff003fc00ffe00c38e3c, 0xfe038f44bbf92a3edf6d54faadb99525e9bd6e9adcf96cc2dfbbaa4c4fe0fe00fc0c70ffc003ffc0003fffc00001fffff0000003fff00003ffff00000fc0fc0, 0xf80807f9112a3bfbf77b66733313dd9b9cece7763677e7eef1b30cc918fff808f000f80fffffc0000003ffffffffe000000000003fffffffc000000000fff000]

theorem nd_e8a8c888 : ins_e8a8c888.Nodup := by decide +kernel

theorem spec_e8a8c888 : ∀ j : Fin 512, Nat.testBit 0xe8a8c888 (∑ i : Fin 5, if (ins_e8a8c888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_e8a8c888 : search 4 ins_e8a8c888 = false := by decide +kernel

def gates_e8a8c888 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [5, 9]⟩]

theorem upper_e8a8c888 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8c888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8a8c888, 10, ?_, rfl, ?_⟩

  · simp [gates_e8a8c888]

  · decide +kernel

def ins_e8a8e880 : List W := [0xd77fefdfdff6fefef7cffdf7f7bf7ffebff5f5ff7ddfbeb7f6fb7efdfd77d77fc33f1020300c01818c600380000f000f803c3c3c000f8001c0381c387c30c33f, 0x6dcfddbe7ddf7bdbfa77efdafb7bbbdbdd7eebddbafadbdedbdded7faedd6dcf0cc72241c33006060f801c01c1f000f007c03fc000f00f8e01c0e03f80cd0cc7, 0xbaf9bb73fe7fafed4ffb7fed6fddddbdeeabfeeedfad6dfb6f6effdad7aebaf930f8448e03c01807f000e001fe000f0007ffc0000f000ff00e00ffc0030e30f8, 0x3f9278f4a7ffd547defdb6cfed6eeaa97cef6f74ebb9f96d8fffb5ab1bf83f923f00870ffc001ff80000fffe00000ffff80000000ffff0000fff000003f03f00, 0xc02407f908aa1ff7ef5edb71b188fcce7733b3bb0cce7e7ffdb0da3463ffc024c000f80fffffe0000000fffffffff000000000000ffffffff000000003ffc000]

theorem nd_e8a8e880 : ins_e8a8e880.Nodup := by decide +kernel

theorem spec_e8a8e880 : ∀ j : Fin 512, Nat.testBit 0xe8a8e880 (∑ i : Fin 5, if (ins_e8a8e880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_e8a8e880 : search 6 ins_e8a8e880 = false := by decide +kernel

def gates_e8a8e880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 11]⟩]

theorem upper_e8a8e880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8e880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8a8e880, 12, ?_, rfl, ?_⟩

  · simp [gates_e8a8e880]

  · decide +kernel

def ins_e8e8e800 : List W := [0xd7cfdddf3f6fdbdef8ffddbddb7bbe77fabd5fdbad7edbedbeedbebd7d75d7cfc3cf2220c0c030318e0038000f000f0e0f87c3c0003e00e00e3f8e1c3c30c3cf, 0x6df3bbbcfdf77d7f4f7efedebdbdebbb5fdebdedd7eb6f76f776f75fd6db6df30cf344430300c0c1f001c000f000f00ff007fc0007c00700703ff01fc0c30cf3, 0xbafc7773f7f9fea9ffb7ff6beededdddad7feef6feb5bdbbdbbb7feeabaebafc30fc888c0c0300fe000e000f000f000ffff80000f8003803803fffe0030c30fc, 0x3f55f0f55ffea8fbdbdb6c7bbbe999ff39ecf7479ce7f6c3ffe3da74cff03f553f000f0ff003ff00000ffff0000ffff000000000ffffc003ffc0000003f03f00, 0xc0aa0ffaaaa3fffdededb78cccfeeeefce773bb8e739ffff6c3c6d9b33ffc0aac000f00ffffc0000000ffffffff0000000000000fffffffc0000000003ffc000]

theorem nd_e8e8e800 : ins_e8e8e800.Nodup := by decide +kernel

theorem spec_e8e8e800 : ∀ j : Fin 512, Nat.testBit 0xe8e8e800 (∑ i : Fin 5, if (ins_e8e8e800.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_e8e8e800 : search 4 ins_e8e8e800 = false := by decide +kernel

def gates_e8e8e800 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 9]⟩]

theorem upper_e8e8e800 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8e8e800 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8e8e800, 10, ?_, rfl, ?_⟩

  · simp [gates_e8e8e800]

  · decide +kernel

def ins_eaa8a880 : List W := [0xdfffffdfffefff7f7dfbfffffffdffffefff7f7ffffdfb7ffb7fbffffd6fdfffc3bf0020001800c0c3080000003c0001e00f0f0f0000001c001c0e38fc01c3bf, 0x74cfdabe73bd9dedee8dfbabaceedceb775bb8f72e2eddecddecf67f2eda74cf34472541ce60730303f0070707c0383e01f00ff0003c78e078e0703f00da3447, 0xb979b673f4fea7f6a3bedfd59d776d67bba8fbbb56e36fb56fb57fd9579cb9793878498e0f807c03fc003807f8003fc001fff00003c07f007f007fc0031c3878, 0x3f9271f49fff4aa3f7df6d9fd6bbb6b51f3ddddd9b77c6da77ffdaaa9bf13f923f808e0ff0007ffc00003ff800003ffffe00000003ff80007fff800003e03f80, 0xe2240ff929547ffbfbefb6e6e723ff39ddceeeeee3bbf7ffc6da6d34e3ffe224c000f00fffff800000003fffffffc0000000000003ffffff8000000003ffc000]

theorem nd_eaa8a880 : ins_eaa8a880.Nodup := by decide +kernel

theorem spec_eaa8a880 : ∀ j : Fin 512, Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if (ins_eaa8a880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eaa8a880 : search 7 ins_eaa8a880 = false := by decide +kernel

def gates_eaa8a880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 12]⟩]

theorem upper_eaa8a880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eaa8a880, 13, ?_, rfl, ?_⟩

  · simp [gates_eaa8a880]

  · decide +kernel

def ins_eaa8c880 : List W := [0xf3bfdfdfffb7f7f7df3ffefef7ddfffaffd7e7fefbafadffdb7ebf7dfd6ff3bff19f202000610c0c3180000001c3803e01f0f0f000000071f81c0e387c01f19f, 0x5eeffabeeeffdedee9dfbbbbcfefceef777b9f73e6f6f7b33dedf6ff9eda5eef06670541998030303e0070707e0003c01e00ff0003e3e38000e0703f80da0667, 0xbc79b673e3fa7f6a3bedfd59db76d677b92fbbb56e5b7ed56fb57fdaa79cbc793878498e1e01c03fc003807f8003fc001fff00003c03fc01ff007fc0031c3878, 0x3fc271f43ffcaa3f7df6d9fd6dbb6b25f3bdddd9b77e5b69b7ffdaab4bf13fc23f808e0fe001ffc00003ff800003ffffe00000003ffc0001ffff800003e03f80, 0xe1140ff95551ffbfbf7b6e6e713ff3b9ddceeeee3b9f9fffc6da6d3473ffe114c000f00ffffe00000003fffffffc0000000000003ffffffe0000000003ffc000]

theorem nd_eaa8c880 : ins_eaa8c880.Nodup := by decide +kernel

theorem spec_eaa8c880 : ∀ j : Fin 512, Nat.testBit 0xeaa8c880 (∑ i : Fin 5, if (ins_eaa8c880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eaa8c880 : search 7 ins_eaa8c880 = false := by decide +kernel

def gates_eaa8c880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [11, 12]⟩]

theorem upper_eaa8c880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaa8c880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eaa8c880, 13, ?_, rfl, ?_⟩

  · simp [gates_eaa8c880]

  · decide +kernel

def ins_eaaac080 : List W := [0xf6bfff7ffdff7fbdf3fffbfbd77f7febff3f9ffdee7ebbfebebf9fdfbf5bf6bf369f00800088c0631800000000f0f0f80783c1e00000000f8f8f078f1e00369f, 0x9f6eeaf76fe2ed769df56d6f3be9abbd6dd67ae79babd719dbf57abde6b69f6e8766150c980f0383e003c3c1f000ff003803fe000f0f87800ff0380fe0368766, 0x3b7ad9df3f2ef653bed776677dabe9de74f6eb6bb9cdf52bf9d97ef56ae73b7a38782630e0f003fc003c03fe00ff00003ffc0000f00ff80ff0003ff000c73878, 0x3fc047c1fe44a37bdf666775aecccc9766e773b2dde9664d7d7deca950fc3fc03f80b83f00fffc00003ffc0000ffffffc0000000fff0000fffffc00000f83f80, 0xe4953fead4fffbfff7bbbbb9cffefee7bf7bbddceefe7ffe6e6eb74e9dffe495c000c03fff000000003fffffff00000000000000fffffff00000000000ffc000]

theorem nd_eaaac080 : ins_eaaac080.Nodup := by decide +kernel

theorem spec_eaaac080 : ∀ j : Fin 512, Nat.testBit 0xeaaac080 (∑ i : Fin 5, if (ins_eaaac080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eaaac080 : search 3 ins_eaaac080 = false := by decide +kernel

def gates_eaaac080 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [7, 8]⟩]

theorem upper_eaaac080 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 5 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaaac080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eaaac080, 9, ?_, rfl, ?_⟩

  · simp [gates_eaaac080]

  · decide +kernel

def ins_eac0e880 : List W := [0x579febdfdddbfb77be3ff9bdbdddf7baff2f97f9f397b7b7e6fdbe7cfd7b579f438f14203330060c63800070707c000e03e1f0f00001f1f1c0380e1c3c1b438f, 0xacf7debdfe7defded3dfbefadbeeef5f76f76f76ed7b5b7edbdaf7bfcecfacf78c73214303c018307c0070007f8001f01c01ff0001f001fe01c0701fc0c38c73, 0xb97dbe77e7febfea77edff5bfaf76b7fbadf7bb76f6d7f5b5f6b7fef579db97d307c418c3c00603f8003807f80003e001ffe00003e01fe000e007fe0031c307c, 0x7faa79fa7fff553ffef6dbff7f5bb5adff7bbddbb7bfadadafffdad5bbf27faa3f80860fc0007fc00003ff8000003fffe00000003ffe00000fff800003e03f80, 0xc24007f088a87fbf7b7b6c6c6c63f9c9d39dceec39cfcfcffdb46d1a23ffc240c000f80fffff80000003ffffffffc000000000003ffffffff000000003ffc000]

theorem nd_eac0e880 : ins_eac0e880.Nodup := by decide +kernel

theorem spec_eac0e880 : ∀ j : Fin 512, Nat.testBit 0xeac0e880 (∑ i : Fin 5, if (ins_eac0e880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eac0e880 : search 6 ins_eac0e880 = false := by decide +kernel

def gates_eac0e880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 11]⟩]

theorem upper_eac0e880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac0e880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eac0e880, 12, ?_, rfl, ?_⟩

  · simp [gates_eac0e880]

  · decide +kernel

def ins_eac8e080 : List W := [0xdd9fdbdfdededbdef8ffeafbdb7d7bebfd3e5febce9eedfafb7ebe7d7d79dd9fcd8f2420218130318e0001c00f00e0780f87c3c00007e0703f1c0e1c3c18cd8f, 0x6e77bebdfbef7f7b4f7efdedbdbbb6fdebddbdddb5edb7b76ded77bfd6cf6e770e7341430601c0c1f001c000f000ff807007fc0007c003803fe0701fc0c30e73, 0x36fdf677effbfda9dfb7f767bfdbf5dedafdeed7bd757ed5e7b5ffeecf9e36fd307c098c380600fe000e01ff000f00007ff80000f807fc01c0007fe0031c307c, 0xbfa871f27ff4a8fdfbdb67f6eaecd957dceef766de7e5b69f6ffdad4abf0bfa83f808e0fc007ff00000ffe00000fffff80000000fff80001ffff800003e03f80, 0xc9420ff89547feffededb9b8ccfefe676f773bb8e7bf9fffb8da6d1b33ffc942c000f00ffff80000000ffffffff0000000000000fffffffe0000000003ffc000]

theorem nd_eac8e080 : ins_eac8e080.Nodup := by decide +kernel

theorem spec_eac8e080 : ∀ j : Fin 512, Nat.testBit 0xeac8e080 (∑ i : Fin 5, if (ins_eac8e080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eac8e080 : search 6 ins_eac8e080 = false := by decide +kernel

def gates_eac8e080 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩]

theorem upper_eac8e080 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac8e080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eac8e080, 12, ?_, rfl, ?_⟩

  · simp [gates_eac8e080]

  · decide +kernel

def ins_aaa8a8a8 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7180000000100040008000000001e00001e0000780000001f0007c001f8038e3, 0x9adb55e74f5b3d6db8b97cf56d676d6ceb6dabf396f16daed36bb4e9e5b54d358a24ab1c38e0e3830f07e1e0f83e00f83e00f87801e1e78e01e38078e0154514, 0x2d36ce3f92fd4bf68bdaafdab4ebb6b567b6d73dab7716f565bd59772ad9965a0c4933e03f00fc03f007fe00ffc000ffc000ff8001fe07f001fc007f00198618, 0xf00e3c493ede9223ddecd553e6b5d8c6b51c9d56cdbbbc4989db73a2531e27e0f071c3ffc000fffc0007ffff000000ffffff000001fff80001ffff80001e07e0, 0x4001fc922488fb7beef7199cc7391ce739d8e66771dddf6dcf1262449c1ff880007e03ffffff00000007ffffffffff000000000001fffffffe000000001ff800]

theorem nd_aaa8a8a8 : ins_aaa8a8a8.Nodup := by decide +kernel

theorem spec_aaa8a8a8 : ∀ j : Fin 512, Nat.testBit 0xaaa8a8a8 (∑ i : Fin 5, if (ins_aaa8a8a8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_aaa8a8a8 : search 2 ins_aaa8a8a8 = false := by decide +kernel

def gates_aaa8a8a8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩]

theorem upper_aaa8a8a8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xaaa8a8a8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_aaa8a8a8, 8, ?_, rfl, ?_⟩

  · simp [gates_aaa8a8a8]

  · decide +kernel


end PEqualNP.Outside.L_meta_1423_aux

open PEqualNP.Outside.L_meta_1423_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1423 : ∀ T ∈ ({0xe8a8a888, 0xe8a8c888, 0xe8a8e880, 0xe8e8e800, 0xeaa8a880, 0xeaa8c880, 0xeaaac080, 0xeac0e880, 0xeac8e080, 0xaaa8a8a8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xe8a8a888 8 ins_e8a8a888 nd_e8a8a888 spec_e8a8a888 rfl reject_e8a8a888 upper_e8a8a888 gs o hg he
  · exact replace 0xe8a8c888 6 ins_e8a8c888 nd_e8a8c888 spec_e8a8c888 rfl reject_e8a8c888 upper_e8a8c888 gs o hg he
  · exact replace 0xe8a8e880 8 ins_e8a8e880 nd_e8a8e880 spec_e8a8e880 rfl reject_e8a8e880 upper_e8a8e880 gs o hg he
  · exact replace 0xe8e8e800 6 ins_e8e8e800 nd_e8e8e800 spec_e8e8e800 rfl reject_e8e8e800 upper_e8e8e800 gs o hg he
  · exact replace 0xeaa8a880 9 ins_eaa8a880 nd_eaa8a880 spec_eaa8a880 rfl reject_eaa8a880 upper_eaa8a880 gs o hg he
  · exact replace 0xeaa8c880 9 ins_eaa8c880 nd_eaa8c880 spec_eaa8c880 rfl reject_eaa8c880 upper_eaa8c880 gs o hg he
  · exact replace 0xeaaac080 5 ins_eaaac080 nd_eaaac080 spec_eaaac080 rfl reject_eaaac080 upper_eaaac080 gs o hg he
  · exact replace 0xeac0e880 8 ins_eac0e880 nd_eac0e880 spec_eac0e880 rfl reject_eac0e880 upper_eac0e880 gs o hg he
  · exact replace 0xeac8e080 8 ins_eac8e080 nd_eac8e080 spec_eac8e080 rfl reject_eac8e080 upper_eac8e080 gs o hg he
  · exact replace 0xaaa8a8a8 4 ins_aaa8a8a8 nd_aaa8a8a8 spec_aaa8a8a8 rfl reject_aaa8a8a8 upper_aaa8a8a8 gs o hg he
