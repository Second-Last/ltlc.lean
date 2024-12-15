import Mathlib

inductive LtlcType
  | base : LtlcType -- base type
  | arrow : LtlcType → LtlcType → LtlcType -- arrows/functions
  deriving Repr, BEq
