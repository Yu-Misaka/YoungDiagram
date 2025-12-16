import Mathlib.Tactic.Lemma
-- import YoungDiagram.Basic

-- import Mathlib.Combinatorics.Young.YoungDiagram

-- #check YoungDiagram.le_of_transpose_le

inductive Sign: Type
    | neut
    | pos
    | neg

namespace Sign

inductive Str : Sign →  Type
    | z_str {s : Sign} : Str s
    | neut_succ : Str neut → Str neut
    | p_succ : Str neg → Str pos
    | n_succ : Str pos → Str neg

namespace Str

def len {s : Sign} (st : Str s) : Nat :=
    match st with
    | z_str => 0
    | neut_succ s => 1 + len s
    | p_succ s => 1 + len s
    | n_succ s => 1 + len s

def sig {k : Sign} (st : Str k) : Nat × Nat :=
    match st with
    | z_str => (0, 0)
    | neut_succ z_str => (0,0) -- when odd just round down
    | neut_succ (neut_succ s) =>
        let sign := sig s
        (1 + sign.1 , 1 + sign.2)
    | p_succ s =>
        let sign := sig s -- I think the sign here doesn't matter
        (1 + sign.1, 0 + sign.2)
    | n_succ s =>
        let sign := sig s
        (0 + sign.1, 1 + sign.2)


example : len (neut_succ (neut_succ (neut_succ (neut_succ z_str)))) = 4 := rfl
example : sig (neut_succ (neut_succ (neut_succ (neut_succ z_str)))) = (2, 2) := rfl
example : sig (neut_succ (neut_succ (neut_succ z_str))) = (1, 1) := rfl

-- -+-+
example : len (p_succ (n_succ (p_succ (n_succ z_str)))) = 4 := rfl
example : sig (p_succ (n_succ (p_succ (n_succ z_str)))) = (2, 2) := rfl
-- +-+
example : sig (p_succ (n_succ (p_succ z_str))) = (2, 1) := rfl
-- -+-
example : sig (n_succ (p_succ (n_succ z_str))) = (1, 2) := rfl

lemma len_of_unpolarised_succ (st : Str neut) : len st + 1 = len (neut_succ st) := by
    sorry

theorem signature_of_unpolarised (st : Str neut) : sig st = (len st / 2, len st / 2) := by
    sorry
