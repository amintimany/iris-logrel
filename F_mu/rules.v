From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris_logrel.F_mu Require Export lang.
From iris.prelude Require Import fin_maps.

Section lang_rules.
  Context `{irisG lang Σ}.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Ltac inv_head_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

  Local Hint Constructors head_step.
  Local Hint Resolve to_of_val.

  (** Helper Lemmas for weakestpre. *)

  Lemma wp_bind {E e} K Φ :
    WP e @ E {{ v, WP fill K (# v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
  Proof. exact: wp_ectx_bind. Qed.

  Lemma wp_lam E e1 e2 v Φ :
    to_val e2 = Some v → ▷ WP e1.[e2 /] @ E {{ Φ }} ⊢ WP App (Lam e1) e2 @ E {{ Φ }}.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_head_step' (App _ _) e1.[of_val v /]); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_tlam E e Φ : ▷ WP e @ E {{ Φ }} ⊢ WP TApp (TLam e) @ E {{ Φ }}.
  Proof.
    rewrite -(wp_lift_pure_det_head_step' (TApp _) e); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fold E e v Φ :
    to_val e = Some v → ▷ (|={E}=> Φ v) ⊢ WP Unfold (Fold e) @ E {{ Φ }}.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_head_step' (Unfold _) (of_val v))
      -?wp_value_pvs; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_fst E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v1) ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros ??. rewrite -(wp_lift_pure_det_head_step' (Fst _) e1)
      -?wp_value_pvs; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ (|={E}=> Φ v2) ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
  Proof.
    intros ??. rewrite -(wp_lift_pure_det_head_step' (Snd _) e2)
      -?wp_value_pvs; eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_case_inl E e0 v0 e1 e2 Φ :
    to_val e0 = Some v0 →
    ▷ WP e1.[e0/] @ E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Case _ _ _) (e1.[e0/])); eauto.
    intros; inv_head_step; eauto.
  Qed.

  Lemma wp_case_inr E e0 v0 e1 e2 Φ :
    to_val e0 = Some v0 →
    ▷ WP e2.[e0/] @ E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_head_step' (Case _ _ _) (e2.[e0/])); eauto.
    intros; inv_head_step; eauto.
  Qed.
End lang_rules.
