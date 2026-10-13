(* Ltac2 automation for the three mechanisms that recur in the proofs:

   - clos_solve : membership in a closure, Clos B F.  The function F is decomposed by its
                  syntactic head: a hypothesis, a registered membership lemma, an initial
                  function, a binary operator or a unary operator of the basis.  Membership in
                  the basis (inits/unops/binops) is decided by syntactic comparison, so no
                  potentially expensive conversion between function terms is ever attempted.
   - sound      : soundness of a closure (clos_sound followed by a case analysis of the basis
                  and the hint database prim); the cases it cannot solve are left open.
   - simulate S : a suitable_by_simulation proof from the suitable basis S; the cases that
                  clos_solve and sound cannot solve are left open.

   They are available in ssreflect scripts through the Ltac1 wrappers clos_solve, sound and
   simulate. *)

From Ltac2 Require Import Ltac2 Constr.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat zify.
From UPRF Require Import Basic Prim.

Set Default Proof Mode "Classic".

(** * Syntactic helpers *)

Ltac2 rec app_head (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => app_head f
  | _ => c
  end.

Ltac2 app_args (c : constr) : constr array :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App _ args => args
  | _ => Array.empty
  end.

(* the conclusion of a (possibly quantified) lemma type *)
Ltac2 rec conclusion (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => conclusion b
  | _ => t
  end.

Ltac2 hnf_constr (c : constr) : constr := Std.eval_hnf c.

(* Clos B F  ~>  Some (B, F) *)
Ltac2 clos_parts (t : constr) : (constr * constr) option :=
  let t := hnf_constr t in
  lazy_match! t with
  | Clos ?b ?f => Some (b, f)
  | _ => None
  end.

Ltac2 fail0 () := Control.zero (Tactic_failure None).

(** * Membership in a basis: a disjunction of equalities  x = y1 \/ ... \/ x = yn *)

Ltac2 rec disj_mem () :=
  lazy_match! goal with
  | [ |- ?a = ?b \/ _ ] =>
      if Constr.equal a b then (left; reflexivity) else (right; disj_mem ())
  | [ |- ?a = ?b ] => if Constr.equal a b then reflexivity else fail0 ()
  end.

Ltac2 basis_mem () := hnf; disj_mem ().

(** * Registered membership lemmas (extended in later files with Ltac2 Set) *)

Ltac2 mutable clos_hints () : constr list := [].

(** * Closure membership *)

Ltac2 rec clos_solve0 () :=
  match clos_parts (Control.goal ()) with
  | None => fail0 ()
  | Some p =>
    let (b, f) := p in
    let goal := hnf_constr (Control.goal ()) in
    let hd := app_head f in
    (* 1. a hypothesis *)
    let from_hyp () :=
      let hs := Control.hyps () in
      let rec go l :=
        match l with
        | [] => fail0 ()
        | h :: rest =>
          let (id, _, ty) := h in
          if Constr.equal (hnf_constr ty) goal then Std.exact_no_check (Control.hyp id)
          else go rest
        end in
      go hs in
    (* 2. a hypothesis or registered lemma used as a rule: its conclusion has the same head *)
    let from_hint () :=
      let rec go l :=
        match l with
        | [] => fail0 ()
        | lem :: rest =>
          let concl := conclusion (Constr.type lem) in
          let same :=
            match clos_parts concl with
            | Some q => let (_, g) := q in Constr.equal (app_head g) hd
            | None => false
            end in
          if same then Control.plus (fun () => apply $lem > [ clos_solve0 () .. ])
                                    (fun _ => go rest)
          else go rest
        end in
      let hyps := List.map (fun h => let (id, _, _) := h in Control.hyp id) (Control.hyps ()) in
      go (List.append hyps (clos_hints ())) in
    (* 3. an initial function *)
    let from_init () := apply (@clos_init $b $f) > [ basis_mem () ] in
    (* 4. a binary operator  o g1 g2  and 5. a unary operator  u g *)
    let args := app_args f in
    let n := Array.length args in
    let sub (k : int) := Constr.Unsafe.make (Constr.Unsafe.App hd (Array.sub args 0 k)) in
    let from_binop () :=
      if Int.lt n 2 then fail0 () else
      let o := sub (Int.sub n 2) in
      let g1 := Array.get args (Int.sub n 2) in
      let g2 := Array.get args (Int.sub n 1) in
      apply (@clos_binop $b $o $g1 $g2) > [ basis_mem () | clos_solve0 () | clos_solve0 () ] in
    let from_unop () :=
      if Int.lt n 1 then fail0 () else
      let u := sub (Int.sub n 1) in
      let g := Array.get args (Int.sub n 1) in
      apply (@clos_unop $b $u $g) > [ basis_mem () | clos_solve0 () ] in
    first [ from_hyp () | from_hint () | from_init () | from_binop () | from_unop () ]
  end.

Ltac2 clos_solve () := Control.enter clos_solve0.

(** * Soundness: every function of the closure is primitive recursive *)

#[export] Hint Resolve pr_succ pr_E pr_fst pr_snd pr_cst pr_Sq pr_O pr_Hf pr_Rt
  pr_opPlusI pr_opBox pr_opBoxA pr_opPlus pr_comp' : prim.

(* introduce the arguments and the basis-membership hypothesis, and substitute *)
Ltac2 mem_cases () :=
  ltac1:(intros until 1;
         match goal with H : _ |- _ =>
           hnf in H; repeat match type of H with _ \/ _ => destruct H as [H|H] end
         end; subst; intros).

Ltac2 sound () :=
  apply clos_sound > [ mem_cases (); try (ltac1:(solve [eauto with prim])) .. ].

(** * Simulation of a suitable basis *)

Ltac2 simulate (s : constr) :=
  apply (suitable_by_simulation $s) >
    [ mem_cases (); Control.enter (fun () => try (clos_solve0 ()))
    | mem_cases (); Control.enter (fun () => try (clos_solve0 ()))
    | mem_cases (); Control.enter (fun () => try (clos_solve0 ()))
    | try (sound ()) ].

(** * Ltac1 wrappers for ssreflect scripts *)

Ltac clos_solve := ltac2:(clos_solve ()).
Ltac sound := ltac2:(sound ()).
Tactic Notation "simulate" constr(s) :=
  let f := ltac2:(s |- simulate (Option.get (Ltac1.to_constr s))) in f s.
