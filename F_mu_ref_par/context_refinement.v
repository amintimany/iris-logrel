Require Import iris_logrel.prelude.base.
From iris_logrel.F_mu_ref_par Require Import lang typing rules_binary
        rules logrel_binary fundamental_binary.

Local Notation expr := (expr lang).

Inductive context_item : Type :=
| CTX_Lam
| CTX_AppL (e2 : expr)
| CTX_AppR (e1 : expr)
(* Products *)
| CTX_PairL (e2 : expr)
| CTX_PairR (e1 : expr)
| CTX_Fst
| CTX_Snd
(* Sums *)
| CTX_InjL
| CTX_InjR
| CTX_CaseL (e1 : expr) (e2 : expr)
| CTX_CaseM (e0 : expr) (e2 : expr)
| CTX_CaseR (e0 : expr) (e1 : expr)
(* Nat bin op *)
| CTX_NBOPL (op : NatBinOP) (e2 : expr)
| CTX_NBOPR (op : NatBinOP) (e1 : expr)
(* If *)
| CTX_IfL (e1 : expr) (e2 : expr)
| CTX_IfM (e0 : expr) (e2 : expr)
| CTX_IfR (e0 : expr) (e1 : expr)
(* Recursive Types *)
| CTX_Fold
| CTX_Unfold
(* Polymorphic Types *)
| CTX_TLam
| CTX_TApp
(* Concurrency *)
| CTX_Fork
(* Reference Types *)
| CTX_Alloc
| CTX_Load
| CTX_StoreL (e2 : expr)
| CTX_StoreR (e1 : expr)
(* Compare and swap used for fine-grained concurrency *)
| CTX_CAS_L (e1 : expr) (e2 : expr)
| CTX_CAS_M (e0 : expr) (e2 : expr)
| CTX_CAS_R (e0 : expr) (e1 : expr).

Fixpoint fill_ctx_item (ctx : context_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_NBOPL op e2 => NBOP op e e2
  | CTX_NBOPR op e1 => NBOP op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_Fold => Fold e
  | CTX_Unfold => Unfold e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_Fork => Fork e
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  | CTX_CAS_L e1 e2 => CAS e e1 e2
  | CTX_CAS_M e0 e2 => CAS e0 e e2
  | CTX_CAS_R e0 e1 => CAS e0 e1 e
  end.

Definition context := list context_item.

Definition fill_ctx K e := foldr fill_ctx_item e K.

Local Open Scope bin_logrel_scope.

(** typed context *)
Inductive typed_context_item :
  context_item → (list type) → type → (list type) → type → Prop :=
| TP_CTX_Lam : ∀ Γ τ τ',
    typed_context_item CTX_Lam (TArrow τ τ' :: τ :: Γ) τ' Γ (TArrow τ τ')
| TP_CTX_AppL (e2 : expr) : ∀ Γ τ τ',
    typed Γ e2 τ →
    typed_context_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
| TP_CTX_AppR (e1 : expr) : ∀ Γ τ τ',
    typed Γ e1 (TArrow τ τ') →
    typed_context_item (CTX_AppR e1) Γ τ Γ τ'
| TP_CTX_PairL (e2 : expr) : ∀ Γ τ τ',
    typed Γ e2 τ' →
    typed_context_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
| TP_CTX_PairR (e1 : expr) : ∀ Γ τ τ',
    typed Γ e1 τ →
    typed_context_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
| TP_CTX_Fst : ∀ Γ τ τ',
    typed_context_item CTX_Fst Γ (TProd τ τ') Γ τ
| TP_CTX_Snd : ∀ Γ τ τ',
    typed_context_item CTX_Snd Γ (TProd τ τ') Γ τ'
| TP_CTX_InjL : ∀ Γ τ τ',
    typed_context_item CTX_InjL Γ τ Γ (TSum τ τ')
| TP_CTX_InjR : ∀ Γ τ τ',
    typed_context_item CTX_InjR Γ τ' Γ (TSum τ τ')
| TP_CTX_CaseL (e1 : expr) (e2 : expr) : ∀ Γ τ1 τ2 τ',
    typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
    typed_context_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
| TP_CTX_CaseM (e0 : expr) (e2 : expr) : ∀ Γ τ1 τ2 τ',
    typed Γ e0 (TSum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
    typed_context_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
| TP_CTX_CaseR (e0 : expr) (e1 : expr) : ∀ Γ τ1 τ2 τ',
    typed Γ e0 (TSum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
    typed_context_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
| TP_CTX_IfL (e1 : expr) (e2 : expr) : ∀ Γ τ,
    typed Γ e1 τ → typed Γ e2 τ →
    typed_context_item (CTX_IfL e1 e2) Γ (TBool) Γ τ
| TP_CTX_IfM (e0 : expr) (e2 : expr) : ∀ Γ τ,
    typed Γ e0 (TBool) → typed Γ e2 τ →
    typed_context_item (CTX_IfM e0 e2) Γ τ Γ τ
| TP_CTX_IfR (e0 : expr) (e1 : expr) : ∀ Γ τ,
    typed Γ e0 (TBool) → typed Γ e1 τ →
    typed_context_item (CTX_IfR e0 e1) Γ τ Γ τ
| TP_CTX_NBOPL op (e2 : expr) : ∀ Γ,
    typed Γ e2 TNat →
    typed_context_item (CTX_NBOPL op e2) Γ TNat Γ (NatBinOP_res_type op)
| TP_CTX_NBOPR op (e1 : expr) : ∀ Γ,
    typed Γ e1 TNat →
    typed_context_item (CTX_NBOPR op e1) Γ TNat Γ (NatBinOP_res_type op)
| TP_CTX_Fold : ∀ Γ τ,
    typed_context_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
| TP_CTX_Unfold : ∀ Γ τ,
    typed_context_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
| TP_CTX_TLam : ∀ Γ τ,
    typed_context_item
      CTX_TLam (map (λ t : type, t.[ren (+1)]) Γ) τ Γ (TForall τ)
| TP_CTX_TApp : ∀ Γ τ τ',
    typed_context_item CTX_TApp Γ (TForall τ) Γ τ.[τ'/]
| TP_CTX_Fork : ∀ Γ,
    typed_context_item CTX_Fork Γ TUnit Γ TUnit
| TPCTX_Alloc : ∀ Γ τ,
    typed_context_item CTX_Alloc Γ τ Γ (Tref τ)
| TP_CTX_Load : ∀ Γ τ,
    typed_context_item CTX_Load Γ (Tref τ) Γ τ
| TP_CTX_StoreL (e2 : expr) : ∀ Γ τ,
    typed Γ e2 τ →
    typed_context_item (CTX_StoreL e2) Γ (Tref τ) Γ TUnit
| TP_CTX_StoreR (e1 : expr) : ∀ Γ τ,
    typed Γ e1 (Tref τ) →
    typed_context_item (CTX_StoreR e1) Γ τ Γ TUnit
| TP_CTX_CasL (e1 : expr)  (e2 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e1 τ → typed Γ e2 τ →
    typed_context_item (CTX_CAS_L e1 e2) Γ (Tref τ) Γ TBool
| TP_CTX_CasM (e0 : expr) (e2 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e0 (Tref τ) → typed Γ e2 τ →
    typed_context_item (CTX_CAS_M e0 e2) Γ τ Γ TBool
| TP_CTX_CasR (e0 : expr) (e1 : expr) : ∀ Γ τ,
    EqType τ → typed Γ e0 (Tref τ) → typed Γ e1 τ →
    typed_context_item (CTX_CAS_R e0 e1) Γ τ Γ TBool.

Lemma typed_context_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_context_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. intros H1 H2; induction H2; simpl; eauto using typed. Qed.

Inductive typed_context :
  context → (list type) → type → (list type) → type → Prop :=
| TPCTX_nil : ∀ Γ τ, typed_context nil Γ τ Γ τ
| TPCTX_cons : ∀ Γ1 τ1 Γ2 τ2 Γ3 τ3 k K,
    typed_context_item k Γ2 τ2 Γ3 τ3 →
    typed_context K Γ1 τ1 Γ2 τ2 →
    typed_context (k :: K) Γ1 τ1 Γ3 τ3.

Lemma typed_context_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_context K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof.
  intros H1 H2; induction H2; simpl; eauto using typed_context_item_typed.
Qed.

Lemma typed_context_n_closed K Γ τ Γ' τ' e :
  (∀ f, e.[iter (List.length Γ) up f] = e) → typed_context K Γ τ Γ' τ' →
  ∀ f, (fill_ctx K e).[iter (List.length Γ') up f] = (fill_ctx K e).
Proof.
  intros H1 H2; induction H2; simpl; auto.
  (induction H => f); asimpl; simpl in *;
    repeat match goal with H : _ |- _ => rewrite map_length in H end;
    try f_equal;
    eauto using typed_n_closed;
    try match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
Qed.

Definition context_refines Γ e e' τ :=
  ∀ K,
    typed_context K Γ τ [] TUnit →
    ∀ thp h v, rtc step ([fill_ctx K e], ∅) ((# v) :: thp, h) →
               ∃ thp' h' v',
                 rtc step ([fill_ctx K e'], ∅) ((# v') :: thp', h').