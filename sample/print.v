Require Import myprint.myprint.

PrintTerm (fun (x:nat) => x).
(* (Lambda x (Ind Coq.Init.Datatypes.nat 0) (Rel 1)) *)

PrintTerm plus.
(* (Const Coq.Init.Nat.add) *)

PrintTerm nat.
(* (Ind Coq.Init.Datatypes.nat 0 nat) *)

PrintTerm O.
(* (Construct Coq.Init.Datatypes.nat 0 1 nat O) *)

PrintTerm S.
(* (Construct Coq.Init.Datatypes.nat 0 2 nat S) *)

PrintTerm S O.
(*
(App
  (Construct Coq.Init.Datatypes.nat 0 2 nat S)
  (Construct Coq.Init.Datatypes.nat 0 1 nat O))
*)

Inductive MutInd1 := MC11 : MutInd1 | MC12 : MutInd2 -> MutInd1
with MutInd2 := MC21 : MutInd2 | MC22 : MutInd1 -> MutInd2.

PrintTerm MutInd1. (* (Ind print.MutInd1 0 MutInd1) *)
PrintTerm MutInd2. (* (Ind print.MutInd1 1 MutInd2) *)
PrintTerm MC11. (* (Construct print.MutInd1 0 1 MutInd1 MC11) *)
PrintTerm MC12. (* (Construct print.MutInd1 0 2 MutInd1 MC12) *)
PrintTerm MC21. (* (Construct print.MutInd1 1 1 MutInd2 MC21) *)
PrintTerm MC22. (* (Construct print.MutInd1 1 2 MutInd2 MC22) *)

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
PrintTerm match (0,true) with (x,y) => x end. (* body x is (Rel 2) *)
PrintTerm match (0,true) with (x,y) => y end. (* body y is (Rel 1) *)
PrintTerm match true with true => 0 | false => 0 end.
PrintTerm match O with O => false | S _ => true end.
PrintTerm match (nil : list bool) with nil => 0 | cons h t => 0 end.

Inductive LetInCstr (T : Type) : Type :=
  | lic : let LT := list T in LT -> LetInCstr T.
PrintTerm match lic nat (0::nil) with lic _ n => n end.
(* ci_cstr_ndecls=[2] ci_cstr_nargs=[1] *)

PrintGlobal LetInCstr.

Inductive I1 (T1 T2 : Type) : Type -> Type :=
| c11 : I1 T1 T2 T1
| c12 : I2 T1 T2 T2 -> I1 T1 T2 T1
with I2 (T1 T2 : Type) : Type -> Type :=
| c21 : I2 T1 T2 T2
| c22 : I1 T1 T2 T1 -> I2 T1 T2 T2.

PrintGlobal I1.

(*
(MutInd
  I1
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=2
  mind_nparams=2
  mind_nparams_rec=2
  mind_params_ctxt=[(T2:Type) (T1:Type)]
  (I1
    mind_arity_ctxt=[(_:Type) (T2:Type) (T1:Type)]
    (c11 (forall T1 T2 : Type, I1 T1 T2 T1))
    (c12 (forall T1 T2 : Type, I2 T1 T2 T2 -> I1 T1 T2 T1)))
  (I2
    mind_arity_ctxt=[(_:Type) (T2:Type) (T1:Type)]
    (c21 (forall T1 T2 : Type, I2 T1 T2 T2))
    (c22 (forall T1 T2 : Type, I1 T1 T2 T1 -> I2 T1 T2 T2))))
*)

Inductive I3 (T1 : Type) (T2 : Type) : Type :=
| c31 : I3 T1 T2
| c32 : I3 T1 bool -> I3 T1 T2.

PrintGlobal I3.
(* mind_nparams_rec=1 because 2nd parameter is not always T2
(MutInd
  I3
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=2
  mind_nparams_rec=1
  mind_params_ctxt=[(T2:Type) (T1:Type)]
  (I3
    mind_arity_ctxt=[(T2:Type) (T1:Type)]
    (c31 (forall T1 T2 : Type, I3 T1 T2))
    (c32 (forall T1 T2 : Type, I3 T1 bool -> I3 T1 T2))))
*)

Inductive I4 (T1 : Type) (T2 : Type) : Type :=
| c41 : I4 T1 T2
| c42 : I4 bool T2 -> I4 T1 T2.

PrintGlobal I4.
(* mind_nparams_rec=0 because 1st parameter is not always T1
(MutInd
  I4
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=2
  mind_nparams_rec=0
  mind_params_ctxt=[(T2:Type) (T1:Type)]
  (I4
    mind_arity_ctxt=[(T2:Type) (T1:Type)]
    (c41 (forall T1 T2 : Type, I4 T1 T2))
    (c42 (forall T1 T2 : Type, I4 bool T2 -> I4 T1 T2))))
*)

Inductive I5 (T1 : Type) (Ts := list T1) (T2 : Type) : Type :=
| c51 : I5 T1 T2
| c52 : I5 T1 T2 -> I5 T1 T2.

PrintGlobal I5.
(* mind_nparams and mind_nparams_rec doesn't count let-binding in the parameters.
(MutInd
  I5
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=2
  mind_nparams_rec=2
  mind_params_ctxt=[(T2:Type) (Ts:Type:=(list I5)) (T1:Type)]
  (I5
    mind_arity_ctxt=[(T2:Type) (Ts:Type:=(list I5)) (T1:Type)]
    (c51 (forall T1 : Type, let Ts := list T1 in forall T2 : Type, I5 T1 T2))
    (c52
      (forall T1 : Type,
       let Ts := list T1 in forall T2 : Type, I5 T1 T2 -> I5 T1 T2))))
*)

PrintTerm fix f x := match x with O => 0 | S y => f y end.
(*
(Fix
  f
  (f
     decarg=0
     (Prod x (Ind Coq.Init.Datatypes.nat 0 nat) (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0)
           ci_npar=0
           ci_cstr_ndecls=[0 1]
           ci_cstr_nargs=[0 1])
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
     decarg=0
     (Prod x (Ind Coq.Init.Datatypes.nat 0 nat) (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       x (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0)
           ci_npar=0
           ci_cstr_ndecls=[0 1]
           ci_cstr_nargs=[0 1])
         (Lambda
           x (Ind Coq.Init.Datatypes.nat 0 nat)
           (Ind Coq.Init.Datatypes.nat 0 nat))
         (Rel 1)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda y (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 3) (Rel 1))))))
  (g
     decarg=0
     (Prod u (Ind Coq.Init.Datatypes.nat 0 nat) (Ind Coq.Init.Datatypes.nat 0 nat))
     (Lambda
       u (Ind Coq.Init.Datatypes.nat 0 nat)
       (Case
         ((Ind Coq.Init.Datatypes.nat 0)
           ci_npar=0
           ci_cstr_ndecls=[0 1]
           ci_cstr_nargs=[0 1])
         (Lambda
           u (Ind Coq.Init.Datatypes.nat 0 nat)
           (Ind Coq.Init.Datatypes.nat 0 nat))
         (Rel 1)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda v (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 4) (Rel 1)))))))
*)

CoInductive Stream : Set := Seq : nat -> Stream -> Stream.

PrintTerm Stream. (* (Ind print.Stream 0 Stream) *)
PrintGlobal Stream.
(*
(MutInd
  Stream
  mind_record=NotRecord
  mind_finite=CoFinite
  mind_ntypes=1
  mind_nparams=0
  mind_nparams_rec=0
  (Stream (Seq (nat -> Stream -> Stream))))
*)

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
    ((Ind Coq.Init.Datatypes.bool 0)
      ci_npar=0
      ci_cstr_ndecls=[0 0]
      ci_cstr_nargs=[0 0])
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
(* decarg=0 means "decreasing on 1st argument" *)

Fixpoint add2 x y :=
  match y with
  | O => x
  | S z => S (add2 x z)
  end.
PrintGlobal add2.
(* decarg=1 means "decreasing on 2nd argument" *)

PrintTerm (1 = 1). (* (App ...) *)
Unset MyPrint ShowProp.
PrintTerm (1 = 1). (* <prop> *)

Require Recdef.

Function addx a b {measure id a} :=
  match a with
  | O => b
  | S n => S (addx n b)
  end.
Proof.
  intros a _ n H.
  unfold id.
  apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

PrintGlobal addx.
PrintGlobal addx_terminate.
Set MyPrint ShowProp.
PrintGlobal addx.
PrintGlobal addx_terminate.

Require Import Int63.
PrintTerm 0%int63.
PrintGlobal Int63.max_int.
