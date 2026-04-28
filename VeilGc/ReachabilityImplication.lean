import VeilGc.Reachability
import VeilGc

set_option linter.unusedSectionVars false

namespace VeilGc
namespace ReachabilityImplication

open Reachability

abbrev MarkColor := VerifiedGc.Color_IndT

open VerifiedGc.Color_IndT

variable {Ptr Offset : Type} [DecidableEq Ptr] [DecidableEq Offset]

/--
The safety property we want after marking:
every object reachable from a root is black.

In the GC model this is the core reason sweeping white objects is safe:
if all root-reachable objects are black, then no root-reachable object is white.
-/
def ReachableRootsAreBlack
    (edges : List (Edge Ptr Offset))
    (roots : Ptr → Prop)
    (color : Ptr → MarkColor) : Prop :=
  ∀ root obj,
    roots root →
    Reach edges root obj →
    color obj = black

/--
This is the direct local tricolor invariant at the end of mark:
all black objects have only black children.
-/
def BlackPointsToBlack
    (edges : List (Edge Ptr Offset))
    (color : Ptr → MarkColor) : Prop :=
  ∀ parent child,
    edgeIn edges parent child →
    color parent = black →
    color child = black

/--
This mirrors your invariant:
if a child is white, all of its parents are white.

Classically this is contrapositive to "a non-white parent cannot point to a
white child". With only black/white/blue colors in mark-complete, it is close
to black-points-to-black, but by itself it is too weak unless combined with
extra color-exclusion facts.
-/
def WhiteChildImpliesWhiteParent
    (edges : List (Edge Ptr Offset))
    (color : Ptr → MarkColor) : Prop :=
  ∀ parent child,
    edgeIn edges parent child →
    color child = white →
    color parent = white

/-- End-of-mark invariant: every root has been marked black. -/
def RootsAreBlack
    (roots : Ptr → Prop)
    (color : Ptr → MarkColor) : Prop :=
  ∀ root, roots root → color root = black

/--
Stronger path-induction lemma:
if a starting object is black, and every black object points only to black
objects, then everything reachable from that starting object is black.
-/
theorem black_reaches_only_black
    {edges : List (Edge Ptr Offset)}
    {color : Ptr → MarkColor}
    (hblack_edges : BlackPointsToBlack edges color)
    {start obj : Ptr}
    (hstart : color start = black)
    (hreach : Reach edges start obj) :
    color obj = black := by
  induction hreach with
  | refl _ =>
      exact hstart
  | step hedge _ ih =>
      apply ih
      exact hblack_edges _ _ hedge hstart

/--
Main implication:
root-black plus black-points-to-black implies every root-reachable object is black.
This is the core mark/sweep safety argument.
-/
theorem safety_from_roots_black_and_black_edges
    {edges : List (Edge Ptr Offset)}
    {roots : Ptr → Prop}
    {color : Ptr → MarkColor}
    (hroots : RootsAreBlack roots color)
    (hblack_edges : BlackPointsToBlack edges color) :
    ReachableRootsAreBlack edges roots color := by
  intro root obj hroot hreach
  exact black_reaches_only_black hblack_edges (hroots root hroot) hreach

/--
Corollary safety property:
a root-reachable object cannot be white, so sweeping white objects preserves live data.
-/
theorem no_reachable_white_from_roots
    {edges : List (Edge Ptr Offset)}
    {roots : Ptr → Prop}
    {color : Ptr → MarkColor}
    (hroots : RootsAreBlack roots color)
    (hblack_edges : BlackPointsToBlack edges color)
    {root obj : Ptr}
    (hroot : roots root)
    (hreach : Reach edges root obj) :
    color obj ≠ white := by
  have hblack :=
    safety_from_roots_black_and_black_edges hroots hblack_edges
      root obj hroot hreach
  intro hwhite
  simp [hblack] at hwhite

end ReachabilityImplication
end VeilGc
