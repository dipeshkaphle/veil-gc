import Std
import Mathlib.Data.Finset.Card
import Veil

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace VeilGc
namespace Reachability

/-- A field-like graph edge: `parent --offset--> child`. -/
@[veil_decl] structure Edge (Ptr Offset : Type) where
  parent : Ptr
  offset : Offset
  child : Ptr
deriving DecidableEq, Repr

variable {Ptr Offset : Type} [DecidableEq Ptr] [DecidableEq Offset]

/--
There is an edge from `parent` to `child` if some field offset connects them.
Reachability follows parent/child links and ignores which offset was used.
-/
def edgeIn (edges : List (Edge Ptr Offset)) (parent child : Ptr) : Prop :=
  ∃ off, Edge.mk parent off child ∈ edges

/--
Mathematical reachability over the edge list.
This is the spec relation: reflexive, and closed under following one field edge.
-/
@[veil_decl] inductive Reach (edges : List (Edge Ptr Offset)) : Ptr → Ptr → Prop where
  | refl (v : Ptr) : Reach edges v v
  | step {src mid dst : Ptr} :
      edgeIn edges src mid →
      Reach edges mid dst →
      Reach edges src dst

/-- Reachability composes: paths can be concatenated. -/
theorem Reach.trans
    {edges : List (Edge Ptr Offset)} {a b c : Ptr}
    (hab : Reach edges a b) (hbc : Reach edges b c) :
    Reach edges a c := by
  induction hab with
  | refl _ => exact hbc
  | step hedge _ ih => exact Reach.step hedge (ih hbc)

/-- Direct children of `src`, obtained by scanning field edges with parent `src`. -/
def childrenOf (edges : List (Edge Ptr Offset)) (src : Ptr) : List (Ptr) :=
  match edges with
  | [] => []
  | edge :: rest =>
      if edge.parent = src then
        edge.child :: childrenOf rest src
      else
        childrenOf rest src

def dfsReachableAux
    (edges : List (Edge Ptr Offset))
    (visited : List (Ptr))
    : List (Ptr) → Nat → List (Ptr)
  | [], _ => visited
  | _, 0 => visited
  | v :: stack, fuel + 1 =>
      if v ∈ visited then
        dfsReachableAux edges visited stack fuel
      else
        let children := childrenOf edges v
        dfsReachableAux edges (v :: visited) (children ++ stack) fuel

/-- A bounded DFS result, using `edges.length + 1` as traversal fuel. -/
def dfsReachable (root : Ptr) (edges : List (Edge Ptr Offset)) : List (Ptr) :=
  dfsReachableAux edges [] [root] (edges.length + 1)

/-- Boolean DFS query: does the bounded DFS list contain `target`? -/
def reachableBool (root target : Ptr) (edges : List (Edge Ptr Offset)) : Bool :=
  (dfsReachable root edges).contains target

/-- Every child returned by `childrenOf` is backed by a real field edge. -/
theorem childrenOf_sound
    {edges : List (Edge Ptr Offset)} {src dst : Ptr} :
    dst ∈ childrenOf edges src → edgeIn edges src dst := by
  induction edges with
  | nil =>
      simp [childrenOf]
  | cons edge rest ih =>
      by_cases hsrc : edge.parent = src
      · simp [childrenOf, hsrc]
        intro h
        cases h with
        | inl hdst =>
            rw [hdst, ← hsrc]
            exact ⟨edge.offset, by simp [edgeIn]⟩
        | inr hrest =>
            rcases ih hrest with ⟨off, hoff⟩
            exact ⟨off, by simp [edgeIn, hoff]⟩
      · simp [childrenOf, hsrc]
        intro hrest
        rcases ih hrest with ⟨off, hoff⟩
        exact ⟨off, by simp [edgeIn, hoff]⟩

theorem children_reachable
    {edges : List (Edge Ptr Offset)} {root src dst : Ptr}
    (hsrc : Reach edges root src)
    (hdst : dst ∈ childrenOf edges src) :
    Reach edges root dst := by
  exact Reach.trans hsrc (Reach.step (childrenOf_sound hdst) (Reach.refl dst))

theorem dfsReachableAux_sound
    {edges : List (Edge Ptr Offset)} {root v : Ptr}
    {visited stack : List (Ptr)} {fuel : Nat}
    (hvisited : ∀ x, x ∈ visited → Reach edges root x)
    (hstack : ∀ x, x ∈ stack → Reach edges root x)
    (hv : v ∈ dfsReachableAux edges visited stack fuel) :
    Reach edges root v := by
  revert visited stack
  induction fuel with
  | zero =>
      intro visited stack hvisited _ hv
      cases stack <;> simp [dfsReachableAux] at hv
      all_goals exact hvisited v hv
  | succ fuel ih =>
      intro visited stack hvisited hstack hv
      cases stack with
      | nil =>
          simp [dfsReachableAux] at hv
          exact hvisited v hv
      | cons head tail =>
          by_cases hseen : head ∈ visited
          · simp [dfsReachableAux, hseen] at hv
            exact ih (visited := visited) (stack := tail) hvisited (by
              intro x hx
              exact hstack x (by simp [hx])) hv
          · simp [dfsReachableAux, hseen] at hv
            exact ih
              (visited := head :: visited)
              (stack := childrenOf edges head ++ tail)
              (by
                intro x hx
                cases List.mem_cons.mp hx with
                | inl hxhead =>
                    rw [hxhead]
                    exact hstack head (by simp)
                | inr hxvisited =>
                    exact hvisited x hxvisited)
              (by
                intro x hx
                have hx' : x ∈ childrenOf edges head ∨ x ∈ tail := by
                  simpa using hx
                cases hx' with
                | inl hchild =>
                    exact children_reachable (hstack head (by simp)) hchild
                | inr htail =>
                    exact hstack x (List.mem_cons.mpr (Or.inr htail)))
              hv

/--
DFS soundness: every vertex returned by the bounded DFS is truly reachable.
This rules out false positives in `dfsReachable`.
-/
theorem dfsReachable_sound
    {edges : List (Edge Ptr Offset)} {root v : Ptr}
    (hv : v ∈ dfsReachable root edges) :
    Reach edges root v := by
  unfold dfsReachable at hv
  exact dfsReachableAux_sound
    (root := root)
    (hvisited := by
      intro x hx
      simp at hx)
    (hstack := by
      intro x hx
      simp at hx
      subst x
      exact Reach.refl _)
    hv

/--
Boolean DFS soundness: if `reachableBool` says yes, then `Reach` holds.
This is the executable-checker-to-spec direction.
-/
theorem reachableBool_sound
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : reachableBool root target edges = true) :
    Reach edges root target := by
  unfold reachableBool at h
  exact dfsReachable_sound (List.contains_iff_mem.mp h)

/--
Reachability using exactly `fuel` edge steps.
This is useful for connecting paths to bounded algorithms.
-/
inductive ReachWithin (edges : List (Edge Ptr Offset)) :
    Nat → Ptr → Ptr → Prop where
  | refl (v : Ptr) : ReachWithin edges 0 v v
  | step {fuel : Nat} {src mid dst : Ptr} :
      edgeIn edges src mid →
      ReachWithin edges fuel mid dst →
      ReachWithin edges (fuel + 1) src dst

/-- Reachability using at most `fuel` edge steps. -/
def ReachAtMost
    (edges : List (Edge Ptr Offset)) (fuel : Nat) (src dst : Ptr) : Prop :=
  ∃ k, k ≤ fuel ∧ ReachWithin edges k src dst

def oneStepDsts (edges : List (Edge Ptr Offset)) (seen : List (Ptr)) :
    List (Ptr) :=
  match edges with
  | [] => []
  | edge :: rest =>
      if edge.parent ∈ seen then
        edge.child :: oneStepDsts rest seen
      else
        oneStepDsts rest seen

def closeStep (edges : List (Edge Ptr Offset)) (seen : List (Ptr)) :
    List (Ptr) :=
  seen ++ oneStepDsts edges seen

/--
Repeatedly expands `seen` by one edge frontier.
After `fuel` rounds it contains everything discovered within that many steps.
-/
def closureFrom (seen : List (Ptr)) (edges : List (Edge Ptr Offset)) :
    Nat → List (Ptr)
  | 0 => seen
  | fuel + 1 => closureFrom (closeStep edges seen) edges fuel

/-- Closure from one root, run for the standard `edges.length + 1` bound. -/
def closureReachable (root : Ptr) (edges : List (Edge Ptr Offset)) :
    List (Ptr) :=
  closureFrom [root] edges (edges.length + 1)

/-- Boolean closure query under the standard bounded fuel. -/
def closureReachableBool
    (root target : Ptr) (edges : List (Edge Ptr Offset)) : Bool :=
  (closureReachable root edges).contains target

theorem oneStepDsts_complete
    {edges : List (Edge Ptr Offset)} {seen : List (Ptr)}
    {src dst : Ptr}
    (hedge : edgeIn edges src dst)
    (hsrc : src ∈ seen) :
    dst ∈ oneStepDsts edges seen := by
  induction edges with
  | nil =>
      simp [edgeIn] at hedge
  | cons edge rest ih =>
      rcases hedge with ⟨off, hedge⟩
      simp at hedge
      simp [oneStepDsts]
      by_cases hmem : edge.parent ∈ seen
      · simp [hmem]
        cases hedge with
        | inl hhead =>
            left
            cases edge
            simp_all
        | inr htail =>
            right
            exact ih ⟨off, htail⟩
      · simp [hmem]
        cases hedge with
        | inl hhead =>
            cases edge
            simp_all
        | inr htail =>
            exact ih ⟨off, htail⟩

theorem closeStep_keeps_seen
    {edges : List (Edge Ptr Offset)} {seen : List (Ptr)} {v : Ptr}
    (hv : v ∈ seen) :
    v ∈ closeStep edges seen := by
  unfold closeStep
  exact List.mem_append.mpr (Or.inl hv)

theorem closeStep_has_edge_dst
    {edges : List (Edge Ptr Offset)} {seen : List (Ptr)}
    {src dst : Ptr}
    (hedge : edgeIn edges src dst)
    (hsrc : src ∈ seen) :
    dst ∈ closeStep edges seen := by
  unfold closeStep
  exact List.mem_append.mpr
    (Or.inr (oneStepDsts_complete hedge hsrc))

/-- Bounded reachability is a valid ordinary reachability proof. -/
theorem ReachWithin.toReach
    {edges : List (Edge Ptr Offset)} {fuel : Nat} {src dst : Ptr}
    (h : ReachWithin edges fuel src dst) :
    Reach edges src dst := by
  induction h with
  | refl v => exact Reach.refl v
  | step hedge _ ih => exact Reach.step hedge ih

theorem ReachAtMost.toReach
    {edges : List (Edge Ptr Offset)} {fuel : Nat} {src dst : Ptr}
    (h : ReachAtMost edges fuel src dst) :
    Reach edges src dst := by
  rcases h with ⟨_, _, hwithin⟩
  exact hwithin.toReach

/-- Every ordinary reachability proof has some finite path length witness. -/
theorem Reach.exists_reachWithin
    {edges : List (Edge Ptr Offset)} {src dst : Ptr}
    (h : Reach edges src dst) :
    ∃ fuel, ReachWithin edges fuel src dst := by
  induction h with
  | refl v =>
      exact ⟨0, ReachWithin.refl v⟩
  | step hedge _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, ReachWithin.step hedge hfuel⟩

theorem closureFrom_complete
    {edges : List (Edge Ptr Offset)} {fuel : Nat} {src dst : Ptr}
    (h : ReachWithin edges fuel src dst) :
    ∀ {seen : List (Ptr)}, src ∈ seen →
      dst ∈ closureFrom seen edges fuel := by
  induction h with
  | refl v =>
      intro seen hseen
      simpa [closureFrom] using hseen
  | step hedge _ ih =>
      intro seen hseen
      simp [closureFrom]
      exact ih (closeStep_has_edge_dst hedge hseen)

theorem closureFrom_keeps_seen
    {edges : List (Edge Ptr Offset)} {fuel : Nat}
    {seen : List (Ptr)} {v : Ptr}
    (hv : v ∈ seen) :
    v ∈ closureFrom seen edges fuel := by
  induction fuel generalizing seen with
  | zero =>
      simpa [closureFrom] using hv
  | succ fuel ih =>
      simp [closureFrom]
      exact ih (closeStep_keeps_seen hv)

theorem closeStep_monotone_seen
    {edges : List (Edge Ptr Offset)} {seen₁ seen₂ : List (Ptr)}
    (hsub : ∀ v, v ∈ seen₁ → v ∈ seen₂) :
    ∀ v, v ∈ closeStep edges seen₁ → v ∈ closeStep edges seen₂ := by
  have oneStep_mono :
      ∀ {edges : List (Edge Ptr Offset)} {v : Ptr},
        v ∈ oneStepDsts edges seen₁ → v ∈ oneStepDsts edges seen₂ := by
    intro edges v hv
    induction edges with
    | nil =>
        simp [oneStepDsts] at hv
    | cons edge rest ih =>
        simp [oneStepDsts] at hv ⊢
        by_cases hmem₁ : edge.parent ∈ seen₁
        · simp [hmem₁] at hv
          have hmem₂ : edge.parent ∈ seen₂ := hsub edge.parent hmem₁
          simp [hmem₂]
          cases hv with
          | inl hvhead => exact Or.inl hvhead
          | inr hvrest => exact Or.inr (ih hvrest)
        · simp [hmem₁] at hv
          by_cases hmem₂ : edge.parent ∈ seen₂
          · simp [hmem₂]
            exact Or.inr (ih hv)
          · simp [hmem₂]
            exact ih hv
  intro v hv
  unfold closeStep at hv ⊢
  rcases List.mem_append.mp hv with hv | hv
  · exact List.mem_append.mpr (Or.inl (hsub v hv))
  · exact List.mem_append.mpr (Or.inr (oneStep_mono hv))

theorem closureFrom_monotone_seen
    {edges : List (Edge Ptr Offset)} {fuel : Nat}
    {seen₁ seen₂ : List (Ptr)}
    (hsub : ∀ v, v ∈ seen₁ → v ∈ seen₂) :
    ∀ v, v ∈ closureFrom seen₁ edges fuel →
      v ∈ closureFrom seen₂ edges fuel := by
  induction fuel generalizing seen₁ seen₂ with
  | zero =>
      intro v hv
      simpa [closureFrom] using hsub v hv
  | succ fuel ih =>
      intro v hv
      simp [closureFrom] at hv ⊢
      exact ih (closeStep_monotone_seen hsub) v hv

theorem closureFrom_monotone_fuel
    {edges : List (Edge Ptr Offset)} {fuel extra : Nat}
    {seen : List (Ptr)} {v : Ptr}
    (hv : v ∈ closureFrom seen edges fuel) :
    v ∈ closureFrom seen edges (fuel + extra) := by
  induction extra with
  | zero =>
      simpa using hv
  | succ extra ih =>
      rw [Nat.add_succ]
      simp [closureFrom]
      exact closureFrom_monotone_seen
        (edges := edges)
        (fuel := fuel + extra)
        (seen₁ := seen)
        (seen₂ := closeStep edges seen)
        (fun x hx => closeStep_keeps_seen hx)
        v ih

theorem closureReachable_complete_within
    {edges : List (Edge Ptr Offset)} {fuel : Nat} {root target : Ptr}
    (h : ReachWithin edges fuel root target) :
    target ∈ closureFrom [root] edges fuel := by
  exact closureFrom_complete h (by simp)

/--
Closure completeness for a known bound:
if `target` is reachable within `fuel` steps, `closureFrom` with that fuel finds it.
-/
theorem closureReachable_complete_atMost
    {edges : List (Edge Ptr Offset)} {fuel : Nat} {root target : Ptr}
    (h : ReachAtMost edges fuel root target) :
    target ∈ closureFrom [root] edges fuel := by
  rcases h with ⟨k, hk, hwithin⟩
  have hmem : target ∈ closureFrom [root] edges k :=
    closureReachable_complete_within hwithin
  have : target ∈ closureFrom [root] edges (k + (fuel - k)) :=
    closureFrom_monotone_fuel hmem
  rwa [Nat.add_sub_of_le hk] at this

/--
Unbounded closure completeness:
if `target` is reachable, then some finite number of closure rounds finds it.
-/
theorem closureReachable_complete
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : Reach edges root target) :
    ∃ fuel, target ∈ closureFrom [root] edges fuel := by
  rcases Reach.exists_reachWithin h with ⟨fuel, hfuel⟩
  exact ⟨fuel, closureReachable_complete_within hfuel⟩

theorem closureReachableBool_complete_within
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : ReachWithin edges (edges.length + 1) root target) :
    closureReachableBool root target edges = true := by
  unfold closureReachableBool closureReachable
  exact List.contains_iff_mem.mpr (closureReachable_complete_within h)

/--
Exact Boolean version of `Reach`.
This is noncomputable because it decides the Prop-level reachability relation directly.
-/
noncomputable def exactReachableBool
    (root target : Ptr) (edges : List (Edge Ptr Offset)) : Bool :=
  by
    classical
    exact if Reach edges root target then true else false

/-- Exact checker soundness: `true` implies the spec relation `Reach`. -/
theorem exactReachableBool_sound
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : exactReachableBool root target edges = true) :
    Reach edges root target := by
  unfold exactReachableBool at h
  by_cases hreach : Reach edges root target
  · exact hreach
  · simp [hreach] at h

/-- Exact checker completeness: the spec relation `Reach` implies `true`. -/
theorem exactReachableBool_complete
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : Reach edges root target) :
    exactReachableBool root target edges = true := by
  unfold exactReachableBool
  simp [h]

/--
A concrete path represented by the actual list of edge records used.
This is used to remove cycles and prove the edge-count bound.
-/
inductive Walk (allowed : List (Edge Ptr Offset)) :
    Ptr → Ptr → List (Edge Ptr Offset) → Prop where
  | nil (v : Ptr) : Walk allowed v v []
  | cons (edge : Edge Ptr Offset) {dst : Ptr} {rest : List (Edge Ptr Offset)} :
      edge ∈ allowed →
      Walk allowed edge.child dst rest →
      Walk allowed edge.parent dst (edge :: rest)

theorem Walk.toReachWithin
    {allowed used : List (Edge Ptr Offset)} {src dst : Ptr}
    (h : Walk allowed src dst used) :
    ReachWithin allowed used.length src dst := by
  induction h with
  | nil v =>
      exact ReachWithin.refl v
  | cons edge hedge _ ih =>
      exact ReachWithin.step ⟨edge.offset, hedge⟩ ih

theorem Walk.suffix_from_mem
    {allowed used : List (Edge Ptr Offset)} {start dst : Ptr}
    {edge : Edge Ptr Offset}
    (hwalk : Walk allowed start dst used)
    (hmem : edge ∈ used) :
    ∃ suffix,
      Walk allowed edge.child dst suffix ∧
      (∀ e, e ∈ suffix → e ∈ used) ∧
      (used.Nodup → edge ∉ suffix ∧ suffix.Nodup) := by
  induction hwalk with
  | nil v =>
      simp at hmem
  | cons head hedge hrest ih =>
      simp at hmem
      cases hmem with
      | inl hhead =>
          subst hhead
          exact ⟨_, hrest, by
            intro e he
            exact List.mem_cons.mpr (Or.inr he), by
            intro hnodup
            exact ⟨hnodup.notMem, hnodup.tail⟩⟩
      | inr htail =>
          rcases ih htail with ⟨suffix, hsuffix, hsub, hnodup_suffix⟩
          exact ⟨suffix, hsuffix, by
            intro e he
            exact List.mem_cons.mpr (Or.inr (hsub e he)), by
            intro hnodup
            exact hnodup_suffix hnodup.tail⟩

/--
Every reachability proof can be represented by a walk with no repeated edge.
This is the cycle-removal/simple-path step.
-/
theorem Reach.exists_nodup_walk
    {edges : List (Edge Ptr Offset)} {src dst : Ptr}
    (h : Reach edges src dst) :
    ∃ used,
      Walk edges src dst used ∧
      used.Nodup ∧
      ∀ edge, edge ∈ used → edge ∈ edges := by
  induction h with
  | refl v =>
      exact ⟨[], Walk.nil v, by simp, by simp⟩
  | @step src mid dst hedge _ ih =>
      rcases ih with ⟨used, hwalk, hnodup, hsub⟩
      rcases hedge with ⟨off, hedge_mem⟩
      let edge : Edge Ptr Offset := Edge.mk src off mid
      have hedge' : edge ∈ edges := hedge_mem
      by_cases hmem : edge ∈ used
      · rcases Walk.suffix_from_mem hwalk hmem with
          ⟨suffix, hsuffix_walk, hsuffix_sub, hsuffix_ok⟩
        have hsuffix_ok' := hsuffix_ok hnodup
        exact ⟨edge :: suffix, Walk.cons edge hedge' hsuffix_walk, by
          exact List.nodup_cons.mpr ⟨hsuffix_ok'.1, hsuffix_ok'.2⟩, by
          intro e he
          cases List.mem_cons.mp he with
          | inl heq =>
              rw [heq]
              exact hedge'
          | inr hsuf =>
              exact hsub e (hsuffix_sub e hsuf)⟩
      · exact ⟨edge :: used, Walk.cons edge hedge' hwalk, by
          exact List.nodup_cons.mpr ⟨hmem, hnodup⟩, by
          intro e he
          cases List.mem_cons.mp he with
          | inl heq =>
              rw [heq]
              exact hedge'
          | inr hused =>
              exact hsub e hused⟩

theorem length_le_of_nodup_subset
    {xs ys : List α} [DecidableEq α]
    (hnodup : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
  have hfin : xs.toFinset ⊆ ys.toFinset := by
    intro x hx
    simp at hx ⊢
    exact hsub x hx
  have hcard := Finset.card_le_card hfin
  have hxs : xs.length ≤ ys.toFinset.card := by
    simpa [List.toFinset_card_of_nodup hnodup] using hcard
  exact hxs.trans (List.toFinset_card_le (l := ys))

/--
Key finite-graph bound:
if `target` is reachable, it is reachable using at most `edges.length` edges.
-/
theorem reach_atMost_edge_bound
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : Reach edges root target) :
    ReachAtMost edges edges.length root target := by
  rcases h.exists_nodup_walk with ⟨used, hwalk, hnodup, hsub⟩
  exact ⟨used.length, length_le_of_nodup_subset hnodup hsub, hwalk.toReachWithin⟩

/-- Same bound with the `edges.length + 1` fuel used by the executable closure. -/
theorem reach_atMost_edge_bound_succ
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : Reach edges root target) :
    ReachAtMost edges (edges.length + 1) root target := by
  rcases reach_atMost_edge_bound h with ⟨k, hk, hwithin⟩
  exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hwithin⟩

/--
Bounded closure completeness:
if `Reach edges root target` holds, the `edges.length + 1` closure checker returns true.
This is the spec-to-executable direction for the bounded checker.
-/
theorem closureReachableBool_complete
    {edges : List (Edge Ptr Offset)} {root target : Ptr}
    (h : Reach edges root target) :
    closureReachableBool root target edges = true := by
  unfold closureReachableBool closureReachable
  exact List.contains_iff_mem.mpr
    (closureReachable_complete_atMost (reach_atMost_edge_bound_succ h))

end Reachability
end VeilGc
