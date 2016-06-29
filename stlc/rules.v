Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import iris_logrel.stlc.lang.

Section lang_rules.
  Context {Σ : iFunctor}.
  Implicit Types P : iProp lang Σ.
  Implicit Types Q : val → iProp lang Σ.

  Ltac inv_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
    | H : prim_step _ _ _ _ _ |- _ => destruct H; subst
    | H : _ = fill ?K ?e |- _ =>
      destruct K as [|[]];
        simpl in H; first [subst e|discriminate H|injection H as H]
    (* ensure that we make progress for each subgoal *)
    | H : head_step ?e _ _ _ _, Hv : of_val ?v = fill ?K ?e |- _ =>
      apply values_head_stuck, (fill_not_val K) in H;
        by rewrite -Hv to_of_val in H (* maybe use a helper lemma here? *)
    | H : head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if e is a variable
                                 and can thus better be avoided. *)
       inversion H; subst; clear H
   end.

  Ltac reshape_val e tac :=
    let rec go e :=
      match e with
      | of_val ?v => v
      | Pair ?e1 ?e2 =>
        let v1 := reshape_val e1 in let v2 := reshape_val e2 in constr:(PairV v1 v2)
      | InjL ?e => let v := reshape_val e in constr:(InjLV v)
      | InjR ?e => let v := reshape_val e in constr:(InjRV v)
      end in let v := go e in first [tac v | fail 2].

  Ltac reshape_expr e tac :=
    let rec go K e :=
      match e with
      | _ => tac (reverse K) e
      | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
      | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
      | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
      | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
      | Fst ?e => go (FstCtx :: K) e
      | Snd ?e => go (SndCtx :: K) e
      | InjL ?e => go (InjLCtx :: K) e
      | InjR ?e => go (InjRCtx :: K) e
      | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
      end in go (@nil ectx_item) e.

  Ltac do_step tac :=
    try match goal with |- language.reducible _ _ => eexists _, _, _ end;
    simpl;
    match goal with
    | |- prim_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
      reshape_expr e1 ltac:(fun K e1' =>
                              eapply Ectx_step with K e1' _; [reflexivity|reflexivity|];
                              econstructor;
                              rewrite ?to_of_val; tac; fail)
    | |- head_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
      econstructor; rewrite ?to_of_val; tac; fail
    end.

  Local Hint Extern 1 => do_step auto.
  Local Hint Extern 1 => inv_step.

  (** Helper Lemmas for weakestpre. *)

  Lemma wp_bind {E e} K Q :
    wp E e (λ v, wp E (fill K (of_val v)) Q) ⊢ wp E (fill K e) Q.
  Proof. apply weakestpre.wp_bind. Qed.

  Lemma wp_lam E e1 e2 v Q :
    to_val e2 = Some v → ▷ wp E e1.[e2 /] Q ⊢ wp E (App (Lam e1) e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (App _ _) e1.[of_val v /] None) //=; auto.
    - by rewrite right_id.
  Qed.

  Lemma wp_fst E e1 v1 e2 v2 Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ Q v1 ⊢ wp E (Fst (Pair e1 e2)) Q.
  Proof.
    intros <-%of_to_val <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Fst (Pair _ _)) (of_val v1) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ Q v2 ⊢ wp E (Snd (Pair e1 e2)) Q.
  Proof.
    intros <-%of_to_val <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Snd (Pair _ _)) (of_val v2) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.

  Lemma wp_case_inl E e0 v0 e1 e2 Q :
    to_val e0 = Some v0 →
    ▷ wp E e1.[e0/] Q ⊢ wp E (Case (InjL e0) e1 e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Case (InjL _) _ _) (e1.[of_val v0/]) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.  

  Lemma wp_case_inr E e0 v0 e1 e2 Q :
    to_val e0 = Some v0 →
    ▷ wp E e2.[e0/] Q ⊢ wp E (Case (InjR e0) e1 e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Case (InjR _) _ _) (e2.[of_val v0/]) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.
End lang_rules.
