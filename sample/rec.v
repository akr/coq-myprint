Require Import myprint.myprint.

Require List.

PrintRec Nat.add.
PrintRec List.nth.

Fixpoint even_p n :=
  match n with
  | O => true
  | S n' => odd_p n'
  end
with odd_p n :=
  match n with
  | O => false
  | S n' => even_p n'
  end.

PrintRec even_p.
PrintRec odd_p.

Section E.
Variable T : Type.
Variable t : T.
Variable f : T.

Fixpoint even_p' n :=
  match n with
  | O => t
  | S n' => odd_p' n'
  end
with odd_p' n :=
  match n with
  | O => f
  | S n' => even_p' n'
  end.

End E.

PrintRec even_p'.
PrintRec odd_p'.

Require Decimal.
PrintRec Decimal.Little.double.
PrintRec Decimal.Little.succ_double.

Require BinPosDef.
PrintRec BinPosDef.Pos.add.
PrintRec BinPosDef.Pos.add_carry.

Module M1.
  Definition even_p'' := Eval cbv delta [even_p] in even_p.
  PrintRec even_p''.
End M1.

Module M2.
  Definition odd_p'' := Eval cbv delta [odd_p] in odd_p.
  PrintRec odd_p''.
End M2.


