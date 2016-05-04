Require Import iris.program_logic.hoare.
Require Import iris.program_logic.lifting.
Require Import iris.algebra.upred_big_op.
Require Import F_mu.lang F_mu.typing F_mu.rules.
Require Import prelude.Vlist.
Import uPred.

(** interp : is a unary logical relation. *)
Section logrel.
  Context {Σ : iFunctor}.
  Implicit Types P Q R : iProp lang Σ.
  Notation "# v" := (of_val v) (at level 20).

  Canonical Structure leibniz_val := leibnizC val.
  Canonical Structure leibniz_var := leibnizC var.

  
  Class Val_to_IProp_Persistent (f : leibniz_val -n> iProp lang Σ) :=
    val_to_iprop_persistent : ∀ v : val, PersistentP ((cofe_mor_car _ _ f) v).

  Arguments Val_to_IProp_Persistent /.

  (** The empty interpretation used, e.g., in weakening proof *)
  Definition empty_interp : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ x, False%I
    |}.
  
  (** Just to get nicer closed forms, we define extend_context_interp in three steps. *)
  Program Definition extend_context_interp_fun1
    (τi : leibniz_val -n> iProp lang Σ)
    (f : leibniz_var -n> leibniz_val -n> iProp lang Σ) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {| cofe_mor_car :=
         λ x,
         match x return leibniz_val -n> iProp lang Σ with
         | O => τi
         | S x' => f x'
         end
    |}.
  
  Program Definition extend_context_interp_fun2
    (τi : leibniz_val -n> iProp lang Σ) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ f, extend_context_interp_fun1 τi f
    |}.
  Next Obligation.
  Proof. intros ???? Hfg x; destruct x; cbn; trivial. Qed.

  Program Definition extend_context_interp :
    (leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ τi, extend_context_interp_fun2 τi
    |}.
  Next Obligation.
  Proof. intros n g h H Δ x y. destruct x; cbn; auto. Qed.
 
  
(*
  Global Instance extend_context_interp_proper :
    Proper ((≡) ==> (≡)) extend_context_interp.
  Proof. intros τ τ' H Δ x; destruct x; cbn; trivial. Qed.
    
  Global Instance extend_context_interp_ne n :
    Proper (dist n ==> dist n) extend_context_interp.
  Proof. intros τ τ' H Δ x; cbn; destruct x; trivial. Qed.
*)  
    
  Program Definition extend_context_interp_apply :
    ((leibniz_var -n> leibniz_val -n> iProp lang Σ)) -n>
    ((leibniz_var -n> leibniz_val -n> iProp lang Σ) -n>
     leibniz_val -n> iProp lang Σ) -n>
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ Δ,
        {|
          cofe_mor_car := λ f,
            {|
              cofe_mor_car := λ g, f (extend_context_interp g Δ)
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; (cbn + idtac);
    try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
  Next Obligation.
  Proof.
    intros n Δ Δ' HΔ f g x.  cbn.
    match goal with
      |- _ _ ?F x ≡{n}≡ _ _ ?G x =>
      assert (F ≡{n}≡ G) as HFG; [|rewrite HFG; trivial]
    end.
    apply cofe_mor_car_ne; trivial. intros y. cbn.
    destruct y; trivial.
  Qed.    

  Definition interp_unit : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, (w = UnitV)%I
    |}.

  Program Definition interp_prod :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, (∃ w1 w2, w = PairV w1 w2 ∧ ▷ τ1i w1 ∧ ▷ τ2i w2)%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn;
    repeat apply exist_ne =>?;
        try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.

(*  Global Instance interp_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_proper =>v. apply exist_proper=> v'.
    repeat apply and_proper; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
  
  Global Instance interp_prod_ne n : Proper (dist n ==> dist n ==> dist n) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_ne =>v. apply exist_ne=> v'.
    repeat apply and_ne; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
*)
  
  Program Definition interp_sum :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, ((∃ w1, w = InjLV w1 ∧ ▷ τ1i w1) ∨
                      (∃ w2, w = InjRV w2 ∧ ▷ τ2i w2))%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn; try apply or_ne;
    try apply exist_ne =>?;
        try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
  
  (*
  Global Instance interp_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_proper; apply exist_proper =>v;
      apply and_proper; try rewrite H1; try rewrite H2; auto.
  Qed.
  
  Global Instance interp_sum_ne n : Proper (dist n ==> dist n ==> dist n) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_ne; apply exist_ne =>v;
      apply and_ne; try rewrite H1; try rewrite H2; auto.
  Qed.
*)
  Program Definition interp_arrow :
    (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τ1i,
        {|
          cofe_mor_car :=
            λ τ2i,
            {|
              cofe_mor_car :=
                λ w, (□ ∀ v, ▷ τ1i v → WP (App (# w) (# v)) @ ⊤ {{τ2i}})%I
            |}
        |}
    |}.
  Solve Obligations with
  repeat intros ?; cbn;
    try apply always_ne;
    try apply forall_ne=>?; try apply impl_ne; trivial;
      try apply wp_ne =>?;
          try match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
(*    
  Global Instance interp_arrow_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper, forall_proper=> v;
      apply impl_proper;
      [rewrite H1; auto| apply wp_proper; auto].
  Qed.
  
  Global Instance interp_arrow_ne n : Proper (dist n ==> dist n ==> dist n) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne, forall_ne=> v;
      apply impl_ne;
      [rewrite H1; auto| apply wp_ne; auto].
  Qed.
*)  
  Program Definition interp_forall :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ τi,
        {|
          cofe_mor_car :=
            λ w,
            (∃ e, w = TLamV e ∧
                  ∀ (τ'i : {f : (leibniz_val -n> iProp lang Σ) |
                            Val_to_IProp_Persistent f}),
                    □ (▷ WP e @ ⊤ {{λ v, (τi (`τ'i) v)}}))%I
        |}
    |}.
  Next Obligation.
  Proof.
    intros τ τ' x y Hxy; cbn. apply exist_ne => e; apply and_ne; auto.
    rewrite Hxy; trivial.
  Qed.
  Next Obligation.
    intros n f g Hfg x; cbn. apply exist_ne => e; apply and_ne; auto.
    apply forall_ne=> P.
    apply always_ne, (contractive_ne _), wp_ne => w.
    rewrite Hfg; trivial.
  Qed.    
(*    
  Global Instance interp_forall_proper : Proper ((≡) ==> (≡)) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_proper => e; apply and_proper; auto.
    apply forall_proper => τ'i.
    apply always_proper, later_proper, wp_proper =>v'.
    rewrite H1; trivial.
  Qed.
    
  Global Instance interp_forall_ne n : Proper (dist n ==> dist n) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_ne => e; apply and_ne; auto.
    apply forall_ne => τ'i.
    apply always_ne, (contractive_ne _), wp_ne=>w.
    rewrite H1; trivial.
  Qed.
*)
  Program Definition interp_rec_pre :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    (leibniz_val -n> iProp lang Σ) -n>
    (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car :=
        λ τi,
        {| cofe_mor_car :=
             λ rec_appr,
             {|
               cofe_mor_car := λ w, (□ (∃ v, w = FoldV v ∧ ▷ (τi rec_appr v)))%I
             |}
        |}
    |}.
  Next Obligation.
  Proof.
    intros τi rec_appr n x y Hxy; rewrite Hxy; trivial.
  Qed.    
  Next Obligation.
  Proof.
    intros τi n f g Hfg x. cbn.
    apply always_ne, exist_ne =>w; rewrite Hfg; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros n τi τi' Hτi f x. cbn.
    apply always_ne, exist_ne =>w; rewrite Hτi; trivial.
  Qed.

  (*
  Global Instance interp_rec_pre_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper, exist_proper=>e; apply and_proper; trivial.
    apply later_proper.
    rewrite H1 H2; trivial.
  Qed.
  
  Global Instance interp_rec_pre_ne n : Proper (dist n ==> dist n ==> dist n) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne, exist_ne=>e; apply and_ne; trivial.
    apply (contractive_ne _).
    rewrite H1 H2; trivial.
  Qed. *)
  Global Instance interp_rec_pre_contr
           (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    :
      Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply always_ne, exist_ne; intros e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    rewrite H; trivial.
  Qed.
  
  Program Definition interp_rec :
    ((leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ)) -n>
    (leibniz_val -n> iProp lang Σ)
    :=
      {|
        cofe_mor_car := λ τi, fixpoint (interp_rec_pre τi)
      |}.
  Next Obligation.
  Proof. intros n f g H; apply fixpoint_ne => z; rewrite H; trivial. Qed.
    

  (*
  Global Instance interp_rec_proper : Proper ((≡) ==> (≡)) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_proper; eauto=>f.
    rewrite H1; trivial.
  Qed.
    
  Global Instance interp_rec_ne n : Proper (dist n ==> dist n) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_ne; eauto=>f.
    rewrite H1; trivial.
  Qed.
*)
  Program Fixpoint interp (τ : type) {struct τ}
    : (leibniz_var -n> (leibniz_val -n> iProp lang Σ)) -n> leibniz_val -n> iProp lang Σ
    :=
      match τ with
        | TUnit => {| cofe_mor_car := λ Δ, interp_unit |}
        | TProd τ1 τ2 =>
          {| cofe_mor_car := λ Δ, interp_prod (interp τ1 Δ) (interp τ2 Δ)|}
        | TSum τ1 τ2 => {| cofe_mor_car := λ Δ,interp_sum (interp τ1 Δ) (interp τ2 Δ)|}
        | TArrow τ1 τ2 => {|cofe_mor_car := λ Δ, interp_arrow (interp τ1 Δ) (interp τ2 Δ)|}
        | TVar v => {| cofe_mor_car :=
                        λ Δ : (leibniz_var -n> (leibniz_val -n> iProp lang Σ)), (Δ v) |}
        | TForall τ' =>
          {| cofe_mor_car := λ Δ,
                             interp_forall (extend_context_interp_apply Δ (interp τ'))|}
        | TRec τ' =>
          {| cofe_mor_car := λ Δ,
                             interp_rec (extend_context_interp_apply Δ (interp τ'))|}
        end%I.
  Solve Obligations with
  repeat intros ?; match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.
(*    
  Lemma interp_closed_irrel
        (k : nat) (τ : type) (HC HC': closed_type k τ)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (v : val)
    : interp k τ HC Δ v ≡ interp k τ HC' Δ v.
  Proof.
    revert k HC HC' Δ v.
    induction τ; intros k HC HC' Δ v; cbn;
    let rec tac :=
        match goal with
        | _ => progress repeat let w := fresh "w" in apply exist_proper => w; tac
        | _ => progress repeat apply and_proper; tac
        | _ => progress repeat apply or_proper; tac
        | _ => progress repeat apply later_proper; tac
        | _ => progress repeat let w := fresh "w" in apply forall_proper => w; tac
        | _ => progress repeat apply always_proper; tac
        | _ => progress repeat apply impl_proper; tac
        | _ => progress repeat apply wp_proper; try intros ?; tac
        | _ => unfold interp_rec; rewrite fixpoint_proper; eauto;
              intros ? ?; unfold interp_rec_pre; cbn; tac
        | _ => auto
        end
    in tac.
    - unfold force_lookup.
      match goal with
        [|- _ (match ?A with |Some _ => _ |None => _ end ?B) _ ≡ _ (match ?A with |Some _ => _ |None => _ end ?C) _] => 
        generalize B; generalize C; destruct A; auto;
        let H := fresh "H" in intros H; inversion H; congruence
      end.
  Qed.

  Lemma interp_closed_irrel_turnstile
        (k : nat) (τ : type) (HC HC': closed_type k τ)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (v : val)
    : interp k τ HC Δ v ⊢ interp k τ HC' Δ v.
  Proof.
    rewrite interp_closed_irrel; trivial.
  Qed.
*)    
  Definition env_subst (vs : list val) (x : var) : expr :=
    from_option (Var x) (of_val <$> vs !! x).
  
  Lemma typed_subst_head_simpl k Δ τ e w ws :
    typed k Δ e τ -> List.length Δ = S (List.length ws) →
    e.[# w .: env_subst ws] = e.[env_subst (w :: ws)]
  .
  Proof.
    intros H1 H2.
    rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
    destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
      by rewrite Hv.
  Qed.

  Class context_interp_Persistent (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    contextinterppersistent : ∀ v : var, Val_to_IProp_Persistent (Δ v).

  Global Instance Val_to_IProp_Persistent_Persistent
           (f : leibniz_val -n> iProp lang Σ)
           {Hf : Val_to_IProp_Persistent f}
           (v : val)
    : PersistentP (f v).
  Proof. apply Hf. Qed.
    
  Global Instance interp_Persistent
         τ (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
         {HΔ : context_interp_Persistent Δ}
    : Val_to_IProp_Persistent (interp τ Δ).
  Proof.
    revert Δ HΔ.
    induction τ; cbn; intros Δ HΔ v; try apply _.
    - rewrite /PersistentP /interp_rec fixpoint_unfold /interp_rec_pre; cbn.
      apply always_intro'; trivial.
    - apply Val_to_IProp_Persistent_Persistent; apply HΔ.
  Qed.

  Global Instance Persistent_context_interp_rel Δ Γ vs
           {HΔ : context_interp_Persistent Δ}
    : PersistentP (Π∧ zip_with(λ τ v, interp τ Δ v) Γ vs)%I.
  Proof. typeclasses eauto. Qed.

  Global Program Instance extend_context_interp_Persistent f Δ
           (Hf : Val_to_IProp_Persistent f)
           {HΔ : context_interp_Persistent Δ}
    : context_interp_Persistent (@extend_context_interp f Δ).
  Next Obligation.
    intros f Δ Hf HΔ v w; destruct v; cbn; trivial.
    apply HΔ.
  Qed.
(*
  Lemma type_context_closed_irrel
        (k : nat) (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) (Γ : list type)
        (vs : list leibniz_val)
        (Hctx Hctx' : closed_ctx k Γ) :
    (Π∧ zip_with
          (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
           ((interp k (` τ) (proj2_sig τ)) Δ) v0)
          (closed_ctx_list k Γ Hctx)
          vs)%I
      ≡
      (Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v)
           (closed_ctx_list k Γ Hctx')
           vs)%I.
  Proof.
    revert vs.
    induction Γ; cbn; auto.
    destruct vs; cbn; auto.
    apply and_proper.
    - apply interp_closed_irrel.
    - apply IHΓ.
  Qed.

  Lemma type_context_closed_irrel_turnstile
        (k : nat) (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) (Γ : list type)
        (vs : list leibniz_val)
        (Hctx Hctx' : closed_ctx k Γ) :
    (Π∧ zip_with
          (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
           ((interp k (` τ) (proj2_sig τ)) Δ) v0)
          (closed_ctx_list k Γ Hctx)
          vs)%I
      ⊢
      (Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v)
           (closed_ctx_list k Γ Hctx')
           vs)%I.
  Proof.
    rewrite type_context_closed_irrel; trivial.
  Qed.
 *)
  (*
  Local Ltac ipropsimpl :=
    repeat
      match goal with
      | [|- (_ ⊢ (_ ∧ _))%I] => eapply and_intro
      | [|- (▷ _ ⊢ ▷ _)%I] => apply later_mono
      | [|- (_ ⊢ ∃ _, _)%I] => rewrite -exist_intro
      | [|- ((∃ _, _) ⊢ _)%I] => let v := fresh "v" in rewrite exist_elim; [|intros v]
      end.

  Local Hint Extern 1 => progress ipropsimpl.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) uconstr(t) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_impl_l; apply and_intro; [
    apply (@always_intro _ _ _ t), forall_intro=> v /=; apply impl_intro_l| eauto with itauto].

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_mono; eauto; intros v; cbn.

  Create HintDb itauto.

  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_r : itauto.
  Local Hint Extern 3 ((_ ∧ _) ⊢ _)%I => rewrite and_elim_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_l : itauto.
  Local Hint Extern 3 (_ ⊢ (_ ∨ _))%I => rewrite -or_intro_r : itauto.
  Local Hint Extern 2 (_ ⊢ ▷ _)%I => etransitivity; [|rewrite -later_intro] : itauto.
  
  Local Ltac value_case := rewrite -wp_value/= ?to_of_val //; auto 2.
   *)

  Local Ltac properness :=
    repeat
      match goal with
      | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
      | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
      | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
      | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
      | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
      | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
      | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
      | |- (□ _)%I ≡ (□ _)%I => apply always_proper
      end.

  Lemma interp_unused_contex_irrel
        (m n : nat)
        (Δ Δ' : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (HΔ : ∀ v, Δ (if lt_dec v m then v else (n + v)) ≡
                     Δ' (if lt_dec v m then v else (n + v)))
        (τ : type)
    :
      interp τ.[iter m up (ren (+n))] Δ ≡ interp τ.[iter m up (ren (+n))] Δ'.
  Proof.
    revert m n Δ Δ' HΔ.
    induction τ; intros m n Δ Δ' HΔ v; cbn; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - properness; trivial; try apply IHτ1; try apply IHτ2; trivial.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn.
      properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply IHτ.
      {
        intros x y. destruct x; cbn; trivial.
        destruct lt_dec.
        - specialize (HΔ x); destruct lt_dec; auto with omega.
        - destruct (n + S x) as [|k] eqn:Heq; trivial.
          specialize (HΔ x); destruct lt_dec; auto with omega.
          replace (n + x) with k in HΔ by omega; trivial.
      }
    -  rewrite iter_up. destruct lt_dec; cbn.
       + specialize (HΔ x); destruct lt_dec; auto with omega.
       + asimpl; unfold ids; cbn.
         specialize (HΔ x); destruct lt_dec; auto with omega.
         replace (m + n + (x - m)) with (n + x) by omega. trivial.
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply IHτ.
      {
        intros x y. destruct x; cbn; trivial.
        destruct lt_dec.
        - specialize (HΔ x); destruct lt_dec; auto with omega.
        - destruct (n + S x) as [|k] eqn:Heq; trivial.
          specialize (HΔ x); destruct lt_dec; auto with omega.
          replace (n + x) with k in HΔ by omega; trivial.
      }
  Qed.
      

  Program Definition hop_context_interp (m n : nat)
    (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ) :
    (leibniz_var -n> leibniz_val -n> iProp lang Σ) :=
    {| cofe_mor_car := λ v, if lt_dec v m then Δ v else Δ (v - n) |}.

  Lemma extend_bofore_hop_context_interp (m n : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τi : leibniz_val -n> iProp lang Σ)
        (v : var)
        (Hv : v > n)
    :
      (extend_context_interp τi (hop_context_interp m n Δ) v)
        ≡ (hop_context_interp (S m) n (extend_context_interp τi Δ) v).
  Proof.      
    revert τi Δ n v Hv.
    induction m; intros τi Δ n v Hv; destruct v; cbn; trivial.
    replace (S v - n) with (S (v - n)) by omega; trivial.
    repeat destruct lt_dec; auto with omega.
    replace (S v - n) with (S (v - n)) by omega; trivial.
  Qed.
  
  Lemma interp_subst_weaken
        (m n : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τ : type)
    : interp τ Δ ≡ interp τ.[iter m up (ren (+n))] (hop_context_interp m n Δ).
  Proof.
    revert m n Δ.
    induction τ; intros m n Δ v; cbn -[extend_context_interp]; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn -[extend_context_interp].
      properness; trivial.
      rewrite IHτ.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply interp_unused_contex_irrel.
      {
      clear. intros [|v]; cbn; trivial.
      repeat (destruct lt_dec; cbn); auto with omega.
      destruct (n + S v - n) eqn:Heq1;
        destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
      match goal with
        [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega; rewrite Heq; trivial
      end.
      }
    - rewrite iter_up.
      asimpl; unfold ids; cbn; destruct lt_dec; cbn; destruct lt_dec; auto with omega.
      replace (m + n + (x - m)) with (x + n) by omega.
      replace (x + n - n) with x; trivial.
      { (** An incompleteness in omega and lia! *)
        clear.
        replace (x + n) with (n + x) by omega.
        induction n; cbn; auto with omega.
        induction x; cbn; trivial.
      }      
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite IHτ.
      apply interp_unused_contex_irrel.
      {
        clear. intros [|v]; cbn; trivial.
        repeat (destruct lt_dec; cbn); auto with omega.
        destruct (n + S v - n) eqn:Heq1;
          destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
        match goal with
          [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega; rewrite Heq; trivial
        end.
      }
  Qed.

  Lemma interp_ren_S (k : nat) (τ : type)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τi : leibniz_val -n> iProp lang Σ)
        (v : leibniz_val)
    : interp τ Δ v ≡ interp τ.[ren (+1)] (extend_context_interp τi Δ) v.
  Proof.
    rewrite (interp_subst_weaken 0 1).
    apply interp_unused_contex_irrel.
    { clear. intros [|v]; cbn; trivial. }
  Qed.

  Lemma interp_subst_iter_up
        (m : nat)
        (Δ : leibniz_var -n> leibniz_val -n> iProp lang Σ)
        (τ : type)
        (τ' : type)
    : interp τ
             (iter m (extend_context_interp empty_interp)
                   (extend_context_interp (interp τ' Δ) Δ))
             ≡ interp τ.[iter m up (τ' .: ids)] 
                          (iter m (extend_context_interp empty_interp) Δ).
  Proof.
    revert m Δ.
    induction τ; intros m Δ v; cbn -[extend_context_interp]; auto.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - properness; trivial; try apply IHτ1; try apply IHτ2.
    - match goal with
        |- _ _ ?f ?x ≡ _ _ ?g ?x =>
        assert (f ≡ g) as Hfg; [|rewrite Hfg; trivial]
      end.
      apply fixpoint_proper => ??; cbn -[extend_context_interp].
      properness; trivial.
      
      rewrite IHτ.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      apply interp_unused_contex_irrel.
      {
      clear. intros [|v]; cbn; trivial.
      repeat (destruct lt_dec; cbn); auto with omega.
      destruct (n + S v - n) eqn:Heq1;
        destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
      match goal with
        [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega; rewrite Heq; trivial
      end.
      }
    - rewrite iter_up.
      asimpl; unfold ids; cbn; destruct lt_dec; cbn; destruct lt_dec; auto with omega.
      replace (m + n + (x - m)) with (x + n) by omega.
      replace (x + n - n) with x; trivial.
      { (** An incompleteness in omega and lia! *)
        clear.
        replace (x + n) with (n + x) by omega.
        induction n; cbn; auto with omega.
        induction x; cbn; trivial.
      }      
    - properness; trivial.
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite IHτ.
      apply interp_unused_contex_irrel.
      {
        clear. intros [|v]; cbn; trivial.
        repeat (destruct lt_dec; cbn); auto with omega.
        destruct (n + S v - n) eqn:Heq1;
          destruct (n + S v) eqn:Heq2; try destruct lt_dec; auto with omega.
        match goal with
          [ |- _ _ _ Δ ?a ≡ _ _ _ Δ ?b] => assert (Heq : a = b) by omega; rewrite Heq; trivial
        end.
      }
    


    
  Lemma interp_subst_iter_up
        (k m : nat)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (Ξ : Vlist (leibniz_val -n> iProp lang Σ) m)
        (τ : type)
        (τ' : type) (HC' : closed_type k τ')
        (HC : closed_type (m + S k) τ)
        (HC'' : closed_type (m + k) τ.[iter m up (τ' .: ids)])
    : interp (m + S k) τ HC (Vlist_app Ξ (Vlist_cons (interp k τ' HC' Δ) Δ))
             ≡ interp (m + k) τ.[iter m up (τ' .: ids)] HC'' (Vlist_app Ξ Δ).
  Proof.
    revert k m Δ Ξ τ' HC' HC HC''.
    induction τ; intros k m Δ Ξ τ' HC' HC HC'' w; cbn; auto.
    - apply exist_proper =>w1; apply exist_proper =>w2;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply or_proper; apply exist_proper =>w1;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply always_proper, forall_proper => w1;
        apply impl_proper; try apply later_proper; try apply wp_proper;
        solve [apply IHτ1|apply IHτ2].
    - apply interp_rec_proper =>f; cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - asimpl in *.
      revert HC''; rewrite iter_up; intros HC''.
      destruct lt_dec.
      + unfold ids, Ids_type; cbn.
        rewrite !force_lookup_l; trivial.
      + remember (x - m) as u.
        destruct (nat_eq_dec x m); try lia.
        * revert HC''; replace u with 0 by lia; asimpl; intros HC''.
          rewrite force_lookup_r; try lia; rewrite -Hequ; intros HC3.
          destruct u; try lia; cbn.
          rewrite -(Vlist_nil_app (Vlist_app Ξ Δ)).
          rewrite -(interp_subst_weaken _ 0 m).
          rewrite Vlist_nil_app; trivial.
        * destruct u; try lia; destruct x; try lia.
          revert HC''; asimpl; intros HC''; inversion HC''.
          unfold ids, Ids_type; cbn.
          rewrite !force_lookup_r; try lia; rewrite -Hequ; intros HC3 HC4.
          rewrite force_lookup_Vlist_cons; try lia; intros HC5.
          revert HC3.
          match goal with
            [|- ∀ _, _ (force_lookup _ ?A _) _ ≡ _ (force_lookup _ ?B _) _] =>
            replace B with A by lia; intros HC3
          end.
          rewrite force_lookup_proper; eauto.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply forall_proper; intros [f Hf].
      apply always_proper, later_proper, wp_proper => w2.
      cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
  Qed.

  Lemma interp_subst
    (k : nat)
    (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
    (τ : type)
    (τ' : type) (HC' : closed_type k τ')
    (HC : closed_type (S k) τ)
    (HC'' : closed_type k τ.[τ'/])
    : interp (S k) τ HC (Vlist_cons (interp k τ' HC' Δ) Δ)
             ≡ interp k τ.[τ'/] HC'' Δ.
  Proof.
    rewrite <- (Vlist_nil_app Δ) at 3.
    rewrite <- (Vlist_nil_app (Vlist_cons ((interp k τ' HC') Δ) Δ)).
    apply (interp_subst_iter_up k 0 Δ Vlist_nil τ τ' HC' HC HC'').
  Qed.

  Lemma zip_with_closed_ctx_list_subst
        (k : nat) (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) (Γ : list type) 
        (Hctx : closed_ctx k Γ)
        (Hctx' : closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ))
        (vs : list leibniz_val) (τi : leibniz_val -n> iProp lang Σ)
    : ((Π∧ zip_with
             (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
              ((interp k (` τ) (proj2_sig τ)) Δ) v)
             (closed_ctx_list k Γ Hctx) vs)%I)
        ≡ (Π∧ zip_with
                (λ (τ : {τ : type | closed_type (S k) τ}) (v : leibniz_val),
                 ((interp (S k) (` τ) (proj2_sig τ)) (Vlist_cons τi Δ)) v)
                (closed_ctx_list (S k) (map (λ t : type, t.[ren (+1)]) Γ) Hctx') vs)%I.
  Proof.
    revert k Δ Hctx Hctx' vs τi.
    induction Γ as [|τ Γ]; intros k Δ Hctx Hctx' vs τi; cbn; trivial.
    destruct vs; cbn; trivial.
    apply and_proper.
    - apply interp_ren_S.
    - apply IHΓ.
  Qed.
*)
End logrel.
