Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import KnotHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Fixpoint Fib (n: nat): nat :=
  match n with
  | 0 => 1
  | S n' =>
    let r := Fib n' in
    match n' with
    | 0 => 1
    | S n'' => r + Fib n''
    end
  end.

Section MAIN.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: SkEnv.t -> list (gname * fspec).
  Variable GlobalStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition fib_spec:    fspec := fun_gen RecStb skenv Fib.

    Definition MainFunStb: list (gname * fspec) := [("fib", fib_spec)].

    Definition main_spec:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (fun varg o =>
                        Own (GRA.embed (knot_frag None)) ** ⌜o = ord_top⌝),
                     (fun vret =>
                        ⌜vret = (Vint (Z.of_nat (Fib 10)))↑⌝)
                )).

    Definition MainStb: list (gname * fspec) := [("fib", fib_spec); ("main", main_spec)].

    Definition MainSbtb: list (gname * fspecbody) :=[("fib", mk_specbody fib_spec (fun _ => trigger (Choose _)));
                                                    ("main", mk_specbody main_spec (fun _ => APC;; Ret (Vint (Z.of_nat (Fib 10)))))].

    Definition SMainSem: SModSem.t := {|
      SModSem.fnsems := MainSbtb;
      SModSem.mn := "Main";
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SMain: SMod.t := {|
    SMod.get_modsem := SMainSem;
    SMod.sk := [("fib", Sk.Gfun)];
  |}
  .

  Definition Main: Mod.t := (SMod.to_tgt GlobalStb) SMain.

End MAIN.