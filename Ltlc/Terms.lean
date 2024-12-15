import Mathlib

import Ltlc.Types

inductive LtlcTerm 
  | var : String → LtlcTerm
  | lam : String → LtlcType → LtlcTerm → LtlcTerm
  | app : LtlcTerm → LtlcTerm → LtlcTerm
  deriving Repr, BEq
