Require Import myprint.myprint.

PrintTerm (fun (x:nat) => x).
(* (Lambda x (Ind Coq.Init.Datatypes.nat 0 nat) (Rel 1 x)) *)

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

PrintGlobal MutInd1.
(*
(MutInd
  MutInd1
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=2
  mind_nparams=0
  mind_nparams_rec=0
  mind_params_ctxt=[]
  (MutInd1
    mind_arity_ctxt=[]
    mind_user_lc=[(MC11 MutInd1) (MC12 (MutInd2 -> MutInd1))]
    mind_nf_lc=[(MC11 MutInd1) (MC12 (MutInd2 -> MutInd1))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1])
  (MutInd2
    mind_arity_ctxt=[]
    mind_user_lc=[(MC21 MutInd2) (MC22 (MutInd1 -> MutInd2))]
    mind_nf_lc=[(MC21 MutInd2) (MC22 (MutInd1 -> MutInd2))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
*)
PrintGlobal MutInd2.
(*
(MutInd
  MutInd2
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=2
  mind_nparams=0
  mind_nparams_rec=0
  mind_params_ctxt=[]
  (MutInd1
    mind_arity_ctxt=[]
    mind_user_lc=[(MC11 MutInd1) (MC12 (MutInd2 -> MutInd1))]
    mind_nf_lc=[(MC11 MutInd1) (MC12 (MutInd2 -> MutInd1))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1])
  (MutInd2
    mind_arity_ctxt=[]
    mind_user_lc=[(MC21 MutInd2) (MC22 (MutInd1 -> MutInd2))]
    mind_nf_lc=[(MC21 MutInd2) (MC22 (MutInd1 -> MutInd2))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
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
(* (Lambda T (Sort Set) (Lambda x (Rel 1 T) (Rel 1 x))) *)

PrintTerm fun (f : nat -> nat) (x : nat) => f x.
(*
(Lambda
  f (Prod _ (Ind Coq.Init.Datatypes.nat 0 nat) (Ind Coq.Init.Datatypes.nat 0 nat))
  (Lambda x (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 2 f) (Rel 1 x))))
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
    (Rel 1 x)
    (Rel 1 x)))
*)

PrintTerm let x := O in x.
(*
(Let
  x (Ind Coq.Init.Datatypes.nat 0 nat)
  (Construct Coq.Init.Datatypes.nat 0 1 nat O)
  (Rel 1 x))
*)

PrintTerm let f := (fun (T : Type) (x : T) => x) in (f bool true, f nat 0).
(*
(Let
  f (Prod T (Sort Type print.5) (Prod x (Rel 1 T) (Rel 2 T)))
  (Lambda T (Sort Type print.5) (Lambda x (Rel 1 T) (Rel 1 x)))
  (App
    (Construct Coq.Init.Datatypes.prod 0 1 prod pair)
    (Ind Coq.Init.Datatypes.bool 0 bool)
    (Ind Coq.Init.Datatypes.nat 0 nat)
    (App
      (Rel 1 f)
      (Ind Coq.Init.Datatypes.bool 0 bool)
      (Construct Coq.Init.Datatypes.bool 0 1 bool true))
    (App
      (Rel 1 f)
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
PrintTerm match (0,true) with (x,y) => x end. (* body x is (Rel 2 x) *)
PrintTerm match (0,true) with (x,y) => y end. (* body y is (Rel 1 y) *)
PrintTerm match true with true => 0 | false => 0 end.
PrintTerm match O with O => false | S _ => true end.
PrintTerm match (nil : list bool) with nil => 0 | cons h t => 0 end.

Inductive LetInCstr (T : Type) : Type :=
  | lic : let LT := list T in LT -> LetInCstr T.
PrintTerm match lic nat (0::nil) with lic _ n => n end.
(* ci_cstr_ndecls=[2] ci_cstr_nargs=[1] *)

PrintGlobal LetInCstr.
(*
(MutInd
  LetInCstr
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=1
  mind_nparams_rec=1
  mind_params_ctxt=[(T:Type)]
  (LetInCstr
    mind_arity_ctxt=[(T:Type)]
    mind_user_lc=[(lic (forall T : Type, let LT := list T in LT -> LetInCstr T))]
    mind_nf_lc=[(lic (forall T : Type, let LT := list T in LT -> LetInCstr T))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[1]
    mind_consnrealdecls=[2]))
*)

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
    mind_user_lc=[(c11 (forall T1 T2 : Type, I1 T1 T2 T1))
      (c12 (forall T1 T2 : Type, I2 T1 T2 T2 -> I1 T1 T2 T1))]
    mind_nf_lc=[(c11 (forall T1 T2 : Type, I1 T1 T2 T1))
      (c12 (forall T1 T2 : Type, I2 T1 T2 T2 -> I1 T1 T2 T1))]
    mind_nrealargs=1
    mind_nrealdecls=1
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1])
  (I2
    mind_arity_ctxt=[(_:Type) (T2:Type) (T1:Type)]
    mind_user_lc=[(c21 (forall T1 T2 : Type, I2 T1 T2 T2))
      (c22 (forall T1 T2 : Type, I1 T1 T2 T1 -> I2 T1 T2 T2))]
    mind_nf_lc=[(c21 (forall T1 T2 : Type, I2 T1 T2 T2))
      (c22 (forall T1 T2 : Type, I1 T1 T2 T1 -> I2 T1 T2 T2))]
    mind_nrealargs=1
    mind_nrealdecls=1
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
*)

Inductive I3 (T1 : Type) (T2 : Type) : Type :=
| c31 : I3 T1 T2
| c32 : I3 T1 bool -> I3 T1 T2.

PrintGlobal I3.
(* mind_nparams_rec=1 != mind_nparams=2 because 2nd parameter is not always T2
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
    mind_user_lc=[(c31 (forall T1 T2 : Type, I3 T1 T2))
      (c32 (forall T1 T2 : Type, I3 T1 bool -> I3 T1 T2))]
    mind_nf_lc=[(c31 (forall T1 T2 : Type, I3 T1 T2))
      (c32 (forall T1 T2 : Type, I3 T1 bool -> I3 T1 T2))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
*)

Inductive I4 (T1 : Type) (T2 : Type) : Type :=
| c41 : I4 T1 T2
| c42 : I4 bool T2 -> I4 T1 T2.

PrintGlobal I4.
(* mind_nparams_rec=0 != mind_nparams=2 because 1st parameter is not always T1
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
    mind_user_lc=[(c41 (forall T1 T2 : Type, I4 T1 T2))
      (c42 (forall T1 T2 : Type, I4 bool T2 -> I4 T1 T2))]
    mind_nf_lc=[(c41 (forall T1 T2 : Type, I4 T1 T2))
      (c42 (forall T1 T2 : Type, I4 bool T2 -> I4 T1 T2))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
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
    mind_user_lc=[(c51
                    (forall T1 : Type,
                     let Ts := list T1 in forall T2 : Type, I5 T1 T2))
      (c52
        (forall T1 : Type,
         let Ts := list T1 in forall T2 : Type, I5 T1 T2 -> I5 T1 T2))]
    mind_nf_lc=[(c51
                  (forall T1 : Type,
                   let Ts := list T1 in forall T2 : Type, I5 T1 T2))
      (c52
        (forall T1 : Type,
         let Ts := list T1 in forall T2 : Type, I5 T1 T2 -> I5 T1 T2))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[0 1]
    mind_consnrealdecls=[0 1]))
*)

Inductive I6 (T1:Type) (L1:=1) (T2:Type) : forall (T3:Type) (L2:=2) (T4:Type), Type :=
| c6 : I6 T1 T2 nat nat.

PrintGlobal I6.
(*
(MutInd
  I6
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=2
  mind_nparams_rec=2
  mind_params_ctxt=[(T2:Type) (L1:nat:=1) (T1:Type)]
  (I6
    mind_arity_ctxt=[(T4:Type)
      (L2:nat:=2)
      (T3:Type)
      (T2:Type)
      (L1:nat:=1)
      (T1:Type)]
    mind_user_lc=[(c6
                    (forall T1 : Type,
                     let L1 := 1 in forall T2 : Type, I6 T1 T2 nat nat))]
    mind_nf_lc=[(c6
                  (forall T1 : Type,
                   let L1 := 1 in forall T2 : Type, I6 T1 T2 nat nat))]
    mind_nrealargs=2
    mind_nrealdecls=3
    mind_consnrealargs=[0]
    mind_consnrealdecls=[0]))
*)

Inductive I7 (T1:id Type) (L1:=(1+2)%nat) (T2:id Type) :
    forall (T3:id Type) (L2:=(2+3)%nat) (T4: id Type), id Type :=
| c7 : id (forall (T5 : id Type) (L3:=(3+4)%nat) (T6 : id Type),
         id (I7 T1 T2 (id T5) (id T6))).

PrintGlobal I7.
(*
(MutInd
  I7
  mind_record=NotRecord
  mind_finite=Finite
  mind_ntypes=1
  mind_nparams=2
  mind_nparams_rec=2
  mind_params_ctxt=[(T2:(id Type)) (L1:nat:=(1 + 2)) (T1:(id Type))]
  (I7
    mind_arity_ctxt=[(T4:(id Type))
      (L2:nat:=(2 + 3))
      (T3:(id Type))
      (T2:(id Type))
      (L1:nat:=(1 + 2))
      (T1:(id Type))]
    mind_user_lc=[(c7
                    (forall T1 : id Type,
                     let L1 := 1 + 2 in
                     forall T2 : id Type,
                     id
                       (forall T5 : id Type,
                        let L3 := 3 + 4 in
                        forall T6 : id Type, id (I7 T1 T2 (id T5) (id T6)))))]
    mind_nf_lc=[(c7
                  (forall T1 : id Type,
                   let L1 := 1 + 2 in
                   forall T2 T5 : id Type,
                   let L3 := 3 + 4 in forall T6 : id Type, I7 T1 T2 (id T5) (id T6)))]
    mind_nrealargs=2
    mind_nrealdecls=3
    mind_consnrealargs=[2]
    mind_consnrealdecls=[3]))
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
         (Rel 1 x)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda y (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 3 f) (Rel 1 y)))))))
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
         (Rel 1 x)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda y (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 3 g) (Rel 1 y))))))
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
         (Rel 1 u)
         (Construct Coq.Init.Datatypes.nat 0 1 nat O)
         (Lambda v (Ind Coq.Init.Datatypes.nat 0 nat) (App (Rel 4 f) (Rel 1 v)))))))
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
  mind_params_ctxt=[]
  (Stream
    mind_arity_ctxt=[]
    mind_user_lc=[(Seq (nat -> Stream -> Stream))]
    mind_nf_lc=[(Seq (nat -> Stream -> Stream))]
    mind_nrealargs=0
    mind_nrealdecls=0
    mind_consnrealargs=[2]
    mind_consnrealdecls=[2]))
*)

PrintTerm cofix from (n:nat) : Stream := Seq n (from (S n)).
(*
(CoFix
  from
  (from (Prod n (Ind Coq.Init.Datatypes.nat 0 nat) (Ind print.Stream 0 Stream))
     (Lambda
       n (Ind Coq.Init.Datatypes.nat 0 nat)
       (App
         (Construct print.Stream 0 1 Stream Seq)
         (Rel 1 n)
         (App
           (Rel 2 from)
           (App (Construct Coq.Init.Datatypes.nat 0 2 nat S) (Rel 1 n)))))))
*)

Set Primitive Projections. (* enables Proj *)
Record Foo : Set := mkFoo { field : nat }.
PrintTerm field (mkFoo 0).
(*
(Proj
  print.field(npars=0,arg=0)
  (App
    (Construct print.Foo 0 1 Foo mkFoo)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)))
*)

Record Bar : Set := mkBar { field0 : nat; field1 : nat }.
PrintTerm field0 (mkBar 0 1).
(*
(Proj
  print.field0(npars=0,arg=0)
  (App
    (Construct print.Bar 0 1 Bar mkBar)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (Construct Coq.Init.Datatypes.nat 0 1 nat O))))
*)
PrintTerm field1 (mkBar 0 1).
(*
(Proj
  print.field1(npars=0,arg=1)
  (App
    (Construct print.Bar 0 1 Bar mkBar)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (Construct Coq.Init.Datatypes.nat 0 1 nat O))))
*)

Record Baz (par:nat) : Set := mkBaz { baz0 : nat; baz1 : nat }.
PrintTerm baz0 0 (mkBaz 0 1 2).
(*
(Proj
  print.baz0(npars=1,arg=0)
  (App
    (Construct print.Baz 0 1 Baz mkBaz)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (Construct Coq.Init.Datatypes.nat 0 1 nat O))
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (App
        (Construct Coq.Init.Datatypes.nat 0 2 nat S)
        (Construct Coq.Init.Datatypes.nat 0 1 nat O)))))
*)
PrintTerm baz1 0 (mkBaz 0 1 2).
(*
(Proj
  print.baz1(npars=1,arg=1)
  (App
    (Construct print.Baz 0 1 Baz mkBaz)
    (Construct Coq.Init.Datatypes.nat 0 1 nat O)
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (Construct Coq.Init.Datatypes.nat 0 1 nat O))
    (App
      (Construct Coq.Init.Datatypes.nat 0 2 nat S)
      (App
        (Construct Coq.Init.Datatypes.nat 0 2 nat S)
        (Construct Coq.Init.Datatypes.nat 0 1 nat O)))))
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
    (Rel 1 b)
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
PrintTerm 0%int63. (* (Int 0) *)
PrintGlobal Int63.max_int. (* (Int 9223372036854775807) *)

Require Floats.
PrintGlobal PrimFloat.zero. (* (Float 0) *)
PrintGlobal PrimFloat.neg_zero. (* (Float 0) *)
PrintGlobal PrimFloat.one. (* (Float 1) *)
PrintGlobal PrimFloat.two. (* (Float 2) *)
PrintGlobal PrimFloat.nan. (* (Float nan) *)
PrintGlobal PrimFloat.infinity. (* (Float inf) *)
PrintGlobal PrimFloat.neg_infinity. (* (Float -inf) *)

Require Import Int63.
Local Open Scope int63_scope.
Require Import PArray.

Definition SampleBoolArray := Eval compute in (make 3 true).[0 <- false].
PrintGlobal SampleBoolArray.
(*
(Array
  (Construct Coq.Init.Datatypes.bool 0 2 bool false)
  (Construct Coq.Init.Datatypes.bool 0 1 bool true)
  (Construct Coq.Init.Datatypes.bool 0 1 bool true)
  |
  (Construct Coq.Init.Datatypes.bool 0 1 bool true)
  :
  (Ind Coq.Init.Datatypes.bool 0 bool))
*)

Definition SampleIntArray := Eval compute in (make 3 100).[0 <- 10].[1 <- 11].[2 <- 12].
PrintGlobal SampleIntArray.
(*
(Array
  (Int 10)
  (Int 11)
  (Int 12)
  |
  (Int 100)
  :
  (Const Coq.Numbers.Cyclic.Int63.Int63.int))
*)
