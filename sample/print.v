Require Import myprint.myprint.

PrintTerm (fun (x:nat) => x).
(* (Lambda x (Ind Coq.Init.Datatypes.nat 0) (Rel 1)) *)

PrintTerm plus.
(* (Const Coq.Init.Nat.add) *)

PrintTerm nat.
(* (Ind Coq.Init.Datatypes.nat 0 nat) *)

PrintTerm O.
(* (Construct Coq.Init.Datatypes.nat 0 1 nat O) *)

PrintTerm S O.
(*
(App
  (Construct Coq.Init.Datatypes.nat 0 2 nat S)
  (Construct Coq.Init.Datatypes.nat 0 1 nat O))
*)

PrintTerm list nat.
(* (App (Ind Coq.Init.Datatypes.list 0 list) (Ind Coq.Init.Datatypes.nat 0 nat)) *)

PrintTerm prod bool nat.
(*
(App
  (Ind Coq.Init.Datatypes.prod 0 prod)
  (Ind Coq.Init.Datatypes.bool 0 bool)
  (Ind Coq.Init.Datatypes.nat 0 nat))
*)

PrintTerm cons true nil.
(*
(App
  (Construct Coq.Init.Datatypes.list 0 2 list cons)
  (Ind Coq.Init.Datatypes.bool 0 bool)
  (Construct Coq.Init.Datatypes.bool 0 1 bool true)
  (App
    (Construct Coq.Init.Datatypes.list 0 1 list nil)
    (Ind Coq.Init.Datatypes.bool 0 bool)))
*)

PrintTerm fun (T : Set) (x : T) => x.
(* (Lambda T (Sort Set) (Lambda x (Rel 1) (Rel 1))) *)

PrintTerm fun (f : nat -> nat) (x : nat) => f x.
(*
(Lambda
  f
    (Prod
      _ (Ind Coq.Init.Datatypes.nat 0 nat)
      (Ind Coq.Init.Datatypes.nat 0 nat))
  (Lambda x (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 2) (Rel 1))))
*)

PrintTerm O : nat.
(*
(Cast (Construct Coq.Init.Datatypes.nat 0 1 nat O)
  DEFAULT
  (Ind Coq.Init.Datatypes.nat 0 nat))
*)

PrintTerm O <: nat.
(*
(Cast (Construct Coq.Init.Datatypes.nat 0 1 nat O)
  VM
  (Ind Coq.Init.Datatypes.nat 0 nat))
*)

PrintTerm forall (x : nat), x = x.
(*
(Prod
  x (Ind Coq.Init.Datatypes.nat 0 nat)
  (App
    (Ind Coq.Init.Logic.eq 0 eq)
    (Ind Coq.Init.Datatypes.nat 0 nat)
    (Rel 1)
    (Rel 1)))
*)

PrintTerm let x := O in x.
(*
(Let
  x (Ind Coq.Init.Datatypes.nat 0 nat)
  (Construct Coq.Init.Datatypes.nat 0 1 nat O)
  (Rel 1))
*)

PrintTerm let f := (fun (T : Type) (x : T) => x) in (f bool true, f nat 0).
(*
(Let
  f (Prod T (Sort Type Top.1) (Prod x (Rel 1) (Rel 2)))
  (Lambda T (Sort Type Top.1) (Lambda x (Rel 1) (Rel 1)))
  (App
    (Construct Coq.Init.Datatypes.prod 0 1 prod pair)
    (Ind Coq.Init.Datatypes.bool 0 bool)
    (Ind Coq.Init.Datatypes.nat 0 nat)
    (App
      (Rel 1)
      (Ind Coq.Init.Datatypes.bool 0 bool)
      (Construct Coq.Init.Datatypes.bool 0 1 bool true))
    (App
      (Rel 1)
      (Ind Coq.Init.Datatypes.nat 0 nat)
      (Construct Coq.Init.Datatypes.nat 0 1 nat O))))
*)

PrintTerm match O with O => false | S _ => true end.
(*
(Case
  ((Ind Coq.Init.Datatypes.nat 0) 0 [0 1] [0 1])
  (Lambda
    x (Ind Coq.Init.Datatypes.nat 0 nat)
    (Ind Coq.Init.Datatypes.bool 0 bool))
  (Construct Coq.Init.Datatypes.nat 0 1 nat O)
  (Construct Coq.Init.Datatypes.bool 0 2 bool false)
  (Lambda
    n (Ind Coq.Init.Datatypes.nat 0 nat)
    (Construct Coq.Init.Datatypes.bool 0 1 bool true)))
*)

PrintTerm match tt with tt => 0 end.
PrintTerm match (0,true) with (_,_) => 0 end.
PrintTerm match true with true => 0 | false => 0 end.
PrintTerm match O with O => false | S _ => true end.
PrintTerm match (nil : list bool) with nil => 0 | cons h t => 0 end.

Inductive LetInCstr (T : Type) : Type :=
  | lic : let LT := list T in LT -> LetInCstr T.
PrintTerm match lic nat (0::nil) with lic _ n => n end.
(* ci_cstr_ndecls=[2] ci_cstr_nargs=[1] *)

PrintTerm fix f x := match x with O => 0 | S y => f y end.
(*
(Fix
  f
  (f
     (Prod
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0) 0 [0 1] [0 1])
         (Lambda
           x (Ind Coq.Init.Datatypes.nat 0 nat)
           (Ind Coq.Init.Datatypes.nat 0 nat))
         (Rel 1)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda y (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 3) (Rel 1)))))))
*)

PrintTerm fix f x := match x with O => 0 | S y => g y end
          with g u := match u with O => 0 | S v => f v end for g.
(*
(Fix
  g
  (f
     (Prod
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0) 0 [0 1] [0 1])
         (Lambda
           x (Ind Coq.Init.Datatypes.nat 0 nat)
           (Ind Coq.Init.Datatypes.nat 0 nat))
         (Rel 1)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda y (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 3) (Rel 1))))))
  (g
     (Prod
       u (Ind Coq.Init.Datatypes.nat 0 nat)
       (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       u (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0) 0 [0 1] [0 1])
         (Lambda
           u (Ind Coq.Init.Datatypes.nat 0 nat)
           (Ind Coq.Init.Datatypes.nat 0 nat))
         (Rel 1)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda v (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 4) (Rel 1)))))))
*)

CoInductive Stream : Set := Seq : nat -> Stream -> Stream.
PrintTerm cofix from (n:nat) : Stream := Seq n (from (S n)).
(*
(CoFix
  0
  from (Prod n (Ind Coq.Init.Datatypes.nat 0 nat) (Ind Top.Stream 0 Stream))
    (Lambda
      n (Ind Coq.Init.Datatypes.nat 0 nat)
      (App
        (Construct Top.Stream 0 1 Stream Seq)
        (Rel 1)
        (App
          (Rel 2)
          (App (Construct Coq.Init.Datatypes.nat 0 2 nat S) (Rel 1)))))))
*)

Set Primitive Projections. (* enables Proj *)
Record Foo : Set := mkFoo { field : nat }.
PrintTerm field (mkFoo 0).
(*
(Proj
  Top.field
  (App
    (Construct Top.Foo 0 1 Foo mkFoo)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)))
*)

Section Sec.
Variable natvar : nat.
PrintTerm natvar.
(* (Var natvar) *)
End Sec.

Goal True.
Proof.
  assert(forall (P : Prop), (P -> P) -> True) as L.
    trivial.
  eapply L.
  intro H.
  PrintType H.
  (* (Evar 49 (Var L)) *)
Abort.

PrintGlobal negb.
(*
(Lambda
  b (Ind Coq.Init.Datatypes.bool 0 bool)
  (Case
    ((Ind Coq.Init.Datatypes.bool 0) 0 [0 0] [0 0])
    (Lambda
      b (Ind Coq.Init.Datatypes.bool 0 bool)
      (Ind Coq.Init.Datatypes.bool 0 bool))
    (Rel 1)
    (Construct Coq.Init.Datatypes.bool 0 2 bool false)
    (Construct Coq.Init.Datatypes.bool 0 1 bool true)))
*)

Fixpoint add1 x y :=
  match x with
  | O => y
  | S z => S (add1 z y)
  end.
PrintGlobal add1.
(* [0] means "decreasing on 1st argument" *)

Fixpoint add2 x y :=
  match y with
  | O => x
  | S z => S (add2 x z)
  end.
PrintGlobal add2.
(* [1] means "decreasing on 2nd argument" *)