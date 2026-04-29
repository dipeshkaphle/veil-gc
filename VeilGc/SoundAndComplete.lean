import Veil
import VeilGc

namespace VeilGc
namespace SoundAndComplete

abbrev Color := VerifiedGc.Color_IndT

open VerifiedGc.Color_IndT

/-- A field-like graph edge: `parent --offset--> child`. -/
@[veil_decl] structure Edge (Ptr Offset : Type) where
  parent : Ptr
  offset : Offset
  child : Ptr
deriving DecidableEq, Repr

def edgeIn (edges : List (Edge Ptr Offset)) (parent child : Ptr) : Prop :=
  ∃ off, Edge.mk parent off child ∈ edges

inductive Reach (edges : List (Edge Ptr Offset)) : Ptr → Ptr → Prop where
  | refl (v : Ptr) : Reach edges v v
  | step {src mid dst : Ptr} :
      edgeIn edges src mid →
      Reach edges mid dst →
      Reach edges src dst

variable {Ptr Offset : Type}

def RootsAreBlack
    (roots : Ptr → Prop)
    (color : Ptr → Color) : Prop :=
  ∀ root, roots root → color root = black

def BlackPointsToBlack
    (edges : List (Edge Ptr Offset))
    (color : Ptr → Color) : Prop :=
  ∀ parent child,
    edgeIn edges parent child →
    color parent = black →
    color child = black

/-
This is because of the following reasons:
- reachables_still_black_after_unreachables_sweeping states that in sweep phase, 
  all reachable tings are preserved (since the black color is preserved)
- We have following invariants after sweep
invariant [all_roots_white_after_sweep] ∀ r , phase = sweep_complete ∧ roots r -> color r = white

-- if a field is white, all it's children are also white
invariant [all_white_points_to_white_after_sweep] ∀ ptr child ,
          phase = sweep_complete ∧
            is_block ptr ∧ is_block child ∧ (∃ off, field ptr off child) ∧
              color ptr = white -> color child = white
- These are symmetrical to the mark invariants but with color white. Same proof but with diff color.
- That means they are not freed as they are white (not blue i.e freed)
-/
def BlackObjectsAreNotFreedAfterSweep
    (markColor sweepColor : Ptr → Color) : Prop :=
  ∀ obj, markColor obj = black → sweepColor obj ≠ blue

theorem reachable_from_black_root_is_black
    {edges : List (Edge Ptr Offset)}
    {color : Ptr → Color}
    (hblack_edges : BlackPointsToBlack edges color)
    {start obj : Ptr}
    (hstart : color start = black)
    (hreach : Reach edges start obj) :
    color obj = black := by
  induction hreach with
  | refl _ =>
      exact hstart
  | step hedge _ ih =>
      exact ih (hblack_edges _ _ hedge hstart)

/--
Soundness handoff to sweep:
`all_roots_marked_black_after_mark_phase` + `no_black_to_white_after_mark`
prove root-reachable objects are black; if sweep preserves black as non-blue,
reachable objects are not freed.
-/
theorem reachable_objects_not_freed_after_sweep
    {edges : List (Edge Ptr Offset)}
    {roots : Ptr → Prop}
    {markColor sweepColor : Ptr → Color}
    (hroots : RootsAreBlack roots markColor)
    (hblack_edges : BlackPointsToBlack edges markColor)
    (hblack_not_freed : BlackObjectsAreNotFreedAfterSweep markColor sweepColor)
    {root obj : Ptr}
    (hroot : roots root)
    (hreach : Reach edges root obj) :
    sweepColor obj ≠ blue :=
  hblack_not_freed obj
    (reachable_from_black_root_is_black hblack_edges (hroots root hroot) hreach)

end SoundAndComplete
end VeilGc
