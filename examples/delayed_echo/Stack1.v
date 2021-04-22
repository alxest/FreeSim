Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Logic.
Require Import Mem1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.embed ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .

  Let pop_spec: fspec := (mk_simple (fun '(llref, xs) => (
                                         (fun varg o =>
                                            Exists ll, ⌜varg = [Vptr llref 0%Z]↑⌝ ** Own (GRA.embed ((llref,0%Z) |-> [ll]))
                                                                               ** (is_list ll xs) ** ⌜o = ord_pure 2⌝),
                                         (fun vret =>
                                            match xs with
                                            | [] => ⌜vret = (Vint (- 1))↑⌝
                                            | xhd :: xtl => ⌜vret = xhd↑⌝ ** (Exists ll', Own (GRA.embed ((llref,0%Z) |-> [ll'])) ** is_list ll' xtl)
                                            end)
                         ))).

  Let pop2_spec: fspec := (mk_simple (fun '(xs, nref) => (
                                        (fun varg o => Exists ll, ⌜varg = [ll; Vptr nref 0%Z]↑⌝ ** (is_list ll xs) **
                                                                           (Exists v, Own (GRA.embed ((nref, 0%Z) |-> [v]))) **
                                                                           ⌜o = ord_pure 2⌝),
                                        (fun vret =>
                                           match xs with
                                           | [] => ⌜vret = Vnullptr↑⌝
                                           | xhd :: xtl => Exists ll', ⌜vret = ll'↑⌝ ** is_list ll' xtl **
                                                                                  Own (GRA.embed ((nref, 0%Z) |-> [xhd]))
                                           end)
                          ))).

(* struct Node* pop2(struct Node* ll, int *n) { *)
(*   if(ll) { *)
(*     int v = (ll)->val; *)
(*     struct Node* next = (ll)->next; *)
(*     free(ll); *)
(*     *n = v; *)
(*     return next; *)
(*   } *)
(*   return NULL; *)
(* } *)

  Let push_spec: fspec := (mk_simple (fun '(x, xs) => (
                                        (fun varg o => Exists ll, ⌜varg = [ll; x]↑⌝ ** is_list ll xs ** ⌜o = ord_pure 2⌝),
                                        (fun vret => Exists ll', is_list ll' (x :: xs) ** ⌜vret = ll'↑⌝)
                          ))).

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("pop", pop_spec) ; ("pop2", pop2_spec) ; ("push", push_spec)].
  Defined.

  Definition StackSbtb: list (gname * fspecbody) :=
    [("pop", mk_specbody pop_spec (fun _ => APC;; trigger (Choose _)));
    ("pop2", mk_specbody pop2_spec (fun _ => APC;; trigger (Choose _)));
    ("push",   mk_specbody push_spec (fun _ => APC;; trigger (Choose _)))
    ]
  .

  Definition SStackSem: SModSem.t := {|
    SModSem.fnsems := StackSbtb;
    SModSem.mn := "Stack";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition StackSem: ModSem.t := (SModSem.to_tgt (MemStb ++ StackStb)) SStackSem.

  Definition SStack: SMod.t := {|
    SMod.get_modsem := fun _ => SStackSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Stack: Mod.t := (SMod.to_tgt (fun _ => MemStb ++ StackStb)) SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
