Require Export prelude.base.
Require Import iris.prelude.gmap.
Require Import iris.program_logic.language.
Require Export Autosubst.Autosubst.

Module lang.
  Definition loc := positive.

  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive expr :=
  | Var (x : var)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* Unit *)
  | Unit
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  (* Polymorphic Types *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Reference Types *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Compare and swap used for fine-grained concurrency *)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr).

  Instance Ids_expr : Ids expr. derive. Defined.
  Instance Rename_expr : Rename expr. derive. Defined.
  Instance Subst_expr : Subst expr. derive. Defined.
  Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.


  Global Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof.
    unfold Decision.
    decide equality; [apply eq_nat_dec | apply loc_dec_eq].
  Defined.

  Inductive val :=
  | LamV (e : {bind 1 of expr})
  | TLamV (e : {bind 1 of expr})
  | UnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (v : val)
  | LocV (l : loc).

  Global Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof.
    unfold Decision; decide equality; try apply expr_dec_eq; apply loc_dec_eq.
  Defined.

  Global Instance val_inh : Inhabited val.
  Proof. constructor. exact UnitV. Qed.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | UnitV => Unit
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | FoldV v => Fold (of_val v)
    | LocV l => Loc l
    end.

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Unit => Some UnitV
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Fold e => v ← to_val e; Some (FoldV v)
    | Loc l => Some (LocV l)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | TAppCtx
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | FoldCtx
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val).

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | TAppCtx => TApp e
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | FoldCtx => Fold e
    | UnfoldCtx => Unfold e
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    | CasLCtx e1 e2 => CAS e e1 e2
    | CasMCtx v0 e2 => CAS (of_val v0) e e2
    | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
    end.

  Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

  Definition state : Type := gmap loc val.

  (** Abbreviation for true and false -- we don't want to add a primitive boolean type
      and its terms *)
  Notation TRUE := (InjL Unit).
  Notation FALSE := (InjR Unit).
  Notation TRUEV := (InjLV UnitV).
  Notation FALSEV := (InjRV UnitV).

  Inductive head_step : expr -> state -> expr -> state -> option expr -> Prop :=
  (* β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ e1.[e2/] σ None
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ e2 σ None
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ None
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ None
  (* Recursive Types *)
  | Unfold_Fold e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ e σ None
  (* Polymorphic Types *)
  | TBeta e σ :
      head_step (TApp (TLam e)) σ e σ None
  (* Concurrency *)
  | ForkS e σ:
      head_step (Fork e) σ Unit σ (Some e)
  (* Reference Types *)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ Unit (<[l:=v]>σ) None
  (* Compare and swap *)
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Loc l) e1 e2) σ FALSE σ None
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Loc l) e1 e2) σ TRUE (<[l:=v2]>σ) None.

  (** Atomic expressions: we don't consider any atomic operations. *)
  Definition atomic (e: expr) :=
    match e with
    | Alloc e => bool_decide (is_Some (to_val e))
    | Load e =>  bool_decide (is_Some (to_val e))
    | Store e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
    | CAS e0 e1 e2 =>
      bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
    | _ => false
    end.

  (** Close reduction under evaluation contexts.
We could potentially make this a generic construction. *)
  Inductive prim_step
            (e1 : expr) (σ1 : state) (e2 : expr) (σ2: state) (ef: option expr) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.

  Instance: Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Instance ectx_fill_inj K : Inj (=) (=) (fill K).
  Proof. red; induction K as [|Ki K IH]; naive_solver. Qed.

  Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K1 (fill K2 e).
  Proof. revert e; induction K1; simpl; auto with f_equal. Qed.

  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    intros [v' Hv']; revert v' Hv'.
    induction K as [|[]]; intros; simplify_option_eq; eauto.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some; eauto using fill_val. Qed.

  Lemma values_head_stuck e1 σ1 e2 σ2 ef :
    head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma values_stuck e1 σ1 e2 σ2 ef : prim_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. intros [??? -> -> ?]; eauto using fill_not_val, values_head_stuck. Qed.

  Lemma atomic_not_val e : atomic e → to_val e = None.
  Proof. destruct e; cbn; intuition auto. Qed.

  Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
  Proof. destruct Ki; cbn; repeat destruct (to_val _); cbn; intuition eauto. Qed.

  Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
  Proof.
    destruct K as [|k K]; cbn; trivial.
    rewrite eq_None_not_Some.
    intros H; apply atomic_fill_item, fill_val in H;
    intuition.
  Qed.

  Lemma atomic_head_step e1 σ1 e2 σ2 ef :
    atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
  Proof.
    intros H1 H2.
    destruct e1; cbn in *; inversion H2;
      try destruct (to_val e1); cbn in *; try inversion H1;
        eauto 2 using to_of_val.
  Qed.

  Lemma atomic_step e1 σ1 e2 σ2 ef :
    atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
  Proof.
    intros Hatomic [K e1' e2' -> -> Hstep].
    assert (K = []) as -> by eauto 10 using atomic_fill, values_head_stuck.
    naive_solver eauto using atomic_head_step.
  Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
    head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  (* When something does a step, and another decomposition of the same expression
has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
other words, [e] also contains the reducible expression *)
  Lemma step_by_val K K' e1 e1' σ1 e2 σ2 ef :
    fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 ef →
    K `prefix_of` K'.
  Proof.
    intros Hfill Hred Hnval; revert K' Hfill.
    induction K as [|Ki K IH]; simpl; intros K' Hfill; auto using prefix_of_nil.
    destruct K' as [|Ki' K']; simplify_eq.
    { exfalso; apply (eq_None_not_Some (to_val (fill K e1)));
      [apply fill_not_val | eapply head_ctx_step_val; erewrite Hfill];
      eauto using fill_not_val, head_ctx_step_val.
    }
    cut (Ki = Ki'); [naive_solver eauto using prefix_of_cons|].
    eauto using fill_item_no_val_inj, values_head_stuck, fill_not_val.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom _ σ) in
    to_val e = Some v → head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None.
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset _)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 ef :
    head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

End lang.

(** Language *)
Program Canonical Structure lang : language := {|
  expr := lang.expr; val := lang.val; state := lang.state;
  of_val := lang.of_val; to_val := lang.to_val;
  atomic := lang.atomic; prim_step := lang.prim_step;
|}.
Solve Obligations with eauto using lang.to_of_val, lang.of_to_val,
  lang.values_stuck, lang.atomic_not_val, lang.atomic_step.

Global Instance lang_ctx K : LanguageCtx lang (lang.fill K).
Proof.
  split.
  * eauto using lang.fill_not_val.
  * intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
    by exists (K ++ K') e1' e2'; rewrite ?lang.fill_app ?Heq1 ?Heq2.
  * intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (lang.step_by_val
      K K'' e1 e1'' σ1 e2'' σ2 ef) as [K' ->]; eauto.
    rewrite lang.fill_app in Heq1; apply (inj _) in Heq1.
    exists (lang.fill K' e2''); rewrite lang.fill_app; split; auto.
    econstructor; eauto.
Qed.

Global Instance lang_ctx_item Ki :
  LanguageCtx lang (lang.fill_item Ki).
Proof. change (LanguageCtx lang (lang.fill [Ki])). by apply _. Qed.

Export lang.