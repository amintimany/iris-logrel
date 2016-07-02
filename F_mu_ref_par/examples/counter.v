From iris.proofmode Require Import invariants ghost_ownership tactics.
From iris_logrel.F_mu_ref_par Require Export examples.lock.
From iris_logrel.F_mu_ref_par Require Import soundness_binary.

Definition CG_increment (x : expr) : expr :=
  Lam (Store x.[ren (+ 2)] (BinOp Add (♯ 1) (Load x.[ren (+ 2)]))).

Definition CG_locked_increment (x l : expr) : expr :=
  with_lock (CG_increment x) l.
Definition CG_locked_incrementV (x l : expr) : val :=
  with_lockV (CG_increment x) l.

Definition counter_read (x : expr) : expr := Lam (Load x.[ren (+2)]).
Definition counter_readV (x : expr) : val := LamV (Load x.[ren (+2)]).

Definition CG_counter_body (x l : expr) : expr :=
  Pair (CG_locked_increment x l) (counter_read x).
Definition CG_counter : expr :=
  App
    (Lam $ App (Lam (CG_counter_body (Var 1) (Var 3)))
               (Alloc (♯ 0)))
    newlock.

Definition FG_increment (x : expr) : expr :=
  Lam $ App
    (Lam $
      (* try increment *)
      If (CAS x.[ren (+4)] (Var 1) (BinOp Add (♯ 1) (Var 1)))
          Unit (* increment succeeds we return unit *)
          (App (Var 2) (Var 3)) (* increment fails, we try again *))
    (Load x.[ren (+2)]) (* read the counter *).
Definition FG_counter_body (x : expr) : expr :=
  Pair (FG_increment x) (counter_read x).
Definition FG_counter : expr :=
  App (Lam (FG_counter_body (Var 1))) (Alloc (♯ 0)).

Section CG_Counter.
  Context `{cfgSG Σ, heapIG Σ}.
  Notation D := (prodC valC valC -n> iPropG lang Σ).
  Implicit Types Δ : listC D.

  (* Coarse-grained increment *)
  Lemma CG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (CG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros H1. repeat econstructor.
    - eapply (context_weakening [_; _]); eauto.
    - eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_increment_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (CG_increment x).[f] = CG_increment x.
  Proof. intros Hx f. unfold CG_increment. asimpl. rewrite ?Hx; trivial. Qed.

  Lemma CG_increment_subst (x : expr) f :
    (CG_increment x).[f] = CG_increment x.[f].
  Proof. unfold CG_increment; asimpl; trivial. Qed.

  Lemma steps_CG_increment E ρ j K x n:
    nclose specN ⊆ E →
    spec_ctx ρ ★ x ↦ₛ (♯v n) ★ j ⤇ fill K (App (CG_increment (Loc x)) Unit)
      ={E}=> j ⤇ fill K (Unit) ★ x ↦ₛ (♯v (S n)).
  Proof.
    iIntros {HNE} "[#Hspec [Hx Hj]]". unfold CG_increment.
    iPvs (step_lam _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iPvs (step_load _ _ j (K ++ [StoreRCtx (LocV _); BinOpRCtx _ (♯v _)])
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iPvs (step_nat_bin_op _ _ j (K ++ [StoreRCtx (LocV _)])
                          _ _ _  with "[Hj]") as "Hj"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial. simpl.
    rewrite ?fill_app. simpl.
    iPvs (step_store _ _ j K _ _ _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    iFrame "Hspec Hj"; trivial.
    iPvsIntro.
    iFrame "Hj Hx"; trivial.
    Unshelve. all: trivial.
  Qed.

  Global Opaque CG_increment.

  Lemma CG_locked_increment_to_val x l :
    to_val (CG_locked_increment x l) = Some (CG_locked_incrementV x l).
  Proof. by rewrite with_lock_to_val. Qed.

  Lemma CG_locked_increment_of_val x l :
    of_val (CG_locked_incrementV x l) = CG_locked_increment x l.
  Proof. by rewrite with_lock_of_val. Qed.

  Global Opaque CG_locked_incrementV.

  Lemma CG_locked_increment_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_locked_increment x l) (TArrow TUnit TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_increment_type.
  Qed.

  Lemma CG_locked_increment_closed (x l : expr) :
    (∀ f, x.[f] = x) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_increment x l).[f] = CG_locked_increment x l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_increment.
    rewrite with_lock_closed; trivial. apply CG_increment_closed; trivial.
  Qed.

  Lemma CG_locked_increment_subst (x l : expr) f :
  (CG_locked_increment x l).[f] = CG_locked_increment x.[f] l.[f].
  Proof.
    unfold CG_locked_increment. simpl.
    rewrite with_lock_subst CG_increment_subst. asimpl; trivial.
  Qed.

  Lemma steps_CG_locked_increment E ρ j K x n l :
    nclose specN ⊆ E →
    spec_ctx ρ ★ x ↦ₛ (♯v n) ★ l ↦ₛ (♭v false)
      ★ j ⤇ fill K (App (CG_locked_increment (Loc x) (Loc l)) Unit)
    ={E}=> j ⤇ fill K Unit ★ x ↦ₛ (♯v S n) ★ l ↦ₛ (♭v false).
  Proof.
    iIntros {HNE} "[#Hspec [Hx [Hl Hj]]]".
    iPvs (steps_with_lock
            _ _ j K _ _ _ _ UnitV UnitV _ _ with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros {K'} "[#Hspec [Hx Hj]]".
      iApply steps_CG_increment; first done. iFrame "Hspec Hj Hx"; trivial.
    - by iFrame "Hspec Hj Hx".
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_increment.

  Lemma counter_read_to_val x : to_val (counter_read x) = Some (counter_readV x).
  Proof. trivial. Qed.

  Lemma counter_read_of_val x : of_val (counter_readV x) = counter_read x.
  Proof. trivial. Qed.

  Global Opaque counter_readV.

  Lemma counter_read_type x Γ :
    typed Γ x (Tref TNat) → typed Γ (counter_read x) (TArrow TUnit TNat).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_; _]); trivial.
  Qed.

  Lemma counter_read_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (counter_read x).[f] = counter_read x.
  Proof. intros H1 f. asimpl. unfold counter_read. by rewrite ?H1. Qed.

  Lemma counter_read_subst (x: expr) f :
    (counter_read x).[f] = counter_read x.[f].
  Proof. unfold counter_read. by asimpl. Qed.

  Lemma steps_counter_read E ρ j K x n :
    nclose specN ⊆ E →
    spec_ctx ρ ★ x ↦ₛ (♯v n)
               ★ j ⤇ fill K (App (counter_read (Loc x)) Unit)
    ={E}=> j ⤇ fill K (♯ n) ★ x ↦ₛ (♯v n).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold counter_read.
    iPvs (step_lam _ _ j K _ Unit with "[Hj]") as "Hj"; eauto.
    asimpl.
    iPvs (step_load _ _ j K with "[Hj Hx]") as "[Hj Hx]"; eauto.
    { by iFrame "Hspec Hj". }
    iPvsIntro. by iFrame "Hj Hx".
  Qed.

  Opaque counter_read.

  Lemma CG_counter_body_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_counter_body x l)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1 H2; repeat econstructor;
      eauto using CG_locked_increment_type, counter_read_type.
  Qed.

  Lemma CG_counter_body_closed (x l : expr) :
    (∀ f, x.[f] = x) → (∀ f, l.[f] = l) →
    ∀ f, (CG_counter_body x l).[f] = CG_counter_body x l.
  Proof.
    intros H1 H2 f. asimpl.
    rewrite CG_locked_increment_closed; trivial. by rewrite counter_read_closed.
  Qed.

  Lemma CG_counter_type Γ :
    typed Γ CG_counter (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type.
    do 2 econstructor; [|do 2 constructor].
    constructor. apply CG_counter_body_type; by constructor.
  Qed.

  Lemma CG_counter_closed f : CG_counter.[f] = CG_counter.
  Proof.
    asimpl; rewrite CG_locked_increment_subst counter_read_subst; by asimpl.
  Qed.

  (* Fine-grained increment *)
  Lemma FG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros H1. do 3 econstructor.
    do 2 econstructor; eauto using EqTNat.
    - eapply (context_weakening [_; _; _; _]); eauto.
    - by constructor.
    - repeat constructor.
    - by constructor.
    - by constructor.
    - eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma FG_increment_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (FG_increment x).[f] = FG_increment x.
  Proof. intros Hx f. asimpl. unfold FG_increment. rewrite ?Hx; trivial. Qed.

  Lemma FG_counter_body_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_counter_body x)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1; econstructor.
    - apply FG_increment_type; trivial.
    - apply counter_read_type; trivial.
  Qed.

  Lemma FG_counter_body_closed (x : expr) :
    (∀ f, x.[f] = x) →
    ∀ f, (FG_counter_body x).[f] = FG_counter_body x.
  Proof.
    intros H1 f. asimpl. unfold FG_counter_body, FG_increment.
    rewrite ?H1. by rewrite counter_read_closed.
  Qed.

  Lemma FG_counter_type Γ :
    typed Γ FG_counter (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type, typed.
    constructor. apply FG_counter_body_type; by constructor.
  Qed.

  Lemma FG_counter_closed f : FG_counter.[f] = FG_counter.
  Proof. asimpl; rewrite counter_read_subst; by asimpl. Qed.

  Definition counterN : namespace := nroot .@ "counter".

  Lemma FG_CG_counter_refinement Δ {HΔ : env_PersistentP Δ} :
    Δ ∥ [] ⊨ FG_counter ≤log≤ CG_counter : TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
  Proof.
    iIntros { [|??] ρ} "#(Hheap & Hspec & HΓ)"; iIntros {j K} "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. }
    iClear "HΓ". cbn -[FG_counter CG_counter].
    rewrite ?empty_env_subst /CG_counter /FG_counter.
    iPvs (steps_newlock _ _ j (K ++ [AppRCtx (LamV _)]) _ with "[Hj]")
      as {l} "[Hj Hl]"; eauto.
    { rewrite fill_app /=. by iFrame. }
    rewrite fill_app /=.
    iPvs (step_lam _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl. rewrite CG_locked_increment_subst /=.
    rewrite counter_read_subst /=.
    iPvs (step_alloc _ _ j (K ++ [AppRCtx (LamV _)]) _ _ _ _ with "[Hj]")
      as {cnt'} "[Hj Hcnt']"; eauto.
    { rewrite fill_app; simpl. by iFrame. }
    rewrite fill_app; simpl.
    iPvs (step_lam _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl. rewrite CG_locked_increment_subst /=.
    rewrite counter_read_subst /=.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    all: trivial.
    iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
      iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
    iApply wp_alloc; trivial; iFrame "Hheap"; iNext; iIntros {cnt} "Hcnt /=".
    iPvsIntro.
    (* establishing the invariant *)
    iAssert ((∃ n, l ↦ₛ (♭v false) ★ cnt ↦ᵢ (♯v n) ★ cnt' ↦ₛ (♯v n) )%I)
      with "[Hl Hcnt Hcnt']" as "Hinv".
    { iExists _. by iFrame. }
    iPvs (inv_alloc counterN with "[Hinv]") as "#Hinv"; trivial.
    { iNext; iExact "Hinv". }
    (* splitting increment and read *)
    iApply wp_lam; trivial. iNext. asimpl.
    rewrite counter_read_subst /=.
    iApply wp_value; simpl.
    { by rewrite counter_read_to_val. }
    iExists (PairV (CG_locked_incrementV _ _) (counter_readV _)); simpl.
    rewrite CG_locked_increment_of_val counter_read_of_val.
    iFrame "Hj".
    iExists (_, _), (_, _); simpl; repeat iSplit; trivial.
    - (* refinement of increment *)
      iAlways. clear j K. iIntros {j K v} "[#Heq Hj]".
      rewrite CG_locked_increment_of_val /=.
      destruct v; iDestruct "Heq" as "[% %]"; simplify_eq/=.
      iLöb as "Hlat".
      iApply wp_lam; trivial. asimpl. iNext.
      (* fine-grained reads the counter *)
      iApply (@wp_bind _ _ _ [AppRCtx (LamV _)]);
        iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
      iInv> counterN as {n} "[Hl [Hcnt Hcnt']]".
      iApply wp_load; [|iFrame "Hheap"]. solve_ndisj.
      iIntros "> {$Hcnt} Hcnt". iPvsIntro.
      iSplitL "Hl Hcnt Hcnt'"; [iExists _; iFrame "Hl Hcnt Hcnt'"; trivial|].
      iApply wp_lam; trivial. asimpl. iNext.
      (* fine-grained performs increment *)
      iApply (@wp_bind _ _ _ [IfCtx _ _; CasRCtx (LocV _) (NatV _)]);
        iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
      iApply wp_nat_bin_op; simpl.
      iNext. iPvsIntro.
      iApply (@wp_bind _ _ _ [IfCtx _ _]);
        iApply wp_wand_l; iSplitR; [iIntros {v} "Hv"; iExact "Hv"|].
      iInv> counterN as {n'} "[Hl [Hcnt Hcnt']]".
      (* performing CAS *)
      destruct (decide (n = n')) as [|Hneq]; subst.
      + (* CAS succeeds *)
        (* In this case, we perform increment in the coarse-grained one *)
        iPvs (steps_CG_locked_increment
                _ _ _ _ _ _ _ _ with "[Hj Hl Hcnt']") as "[Hj [Hcnt' Hl]]".
        { iFrame "Hspec Hcnt' Hl Hj"; trivial. }
        iApply wp_cas_suc; simpl; trivial; [|iFrame "Hheap"]. solve_ndisj.
        iIntros "{$Hcnt} > Hcnt". iPvsIntro.
        iSplitL "Hl Hcnt Hcnt'"; [iExists _; iFrame "Hl Hcnt Hcnt'"; trivial|].
        iApply wp_if_true. iNext. iApply wp_value; trivial.
        iExists UnitV; iFrame; auto.
      + (* CAS fails *)
        (* In this case, we perform a recursive call *)
        iApply (wp_cas_fail _ _ _ (♯v n')); simpl; trivial;
        [inversion 1; subst; auto | | iFrame "Hheap"]. solve_ndisj.
        iIntros "{$Hcnt} > Hcnt". iPvsIntro.
        iSplitL "Hl Hcnt Hcnt'"; [iExists _; iFrame "Hl Hcnt Hcnt'"; trivial|].
        iApply wp_if_false. iNext. by iApply "Hlat".
    - (* refinement of read *)
      iAlways. clear j K. iIntros {j K v} "[#Heq Hj]".
      rewrite ?counter_read_of_val.
      iDestruct "Heq" as "[% %]"; destruct v; simplify_eq/=.
      Transparent counter_read.
      unfold counter_read at 2.
      iApply wp_lam; trivial. simpl.
      iNext. iInv> counterN as {n} "[Hl [Hcnt Hcnt']]".
      iPvs (steps_counter_read with "[Hj Hcnt']") as "[Hj Hcnt']".
      { solve_ndisj. }
      { by iFrame "Hspec Hcnt' Hj". }
      iApply wp_load; [|iFrame "Hheap"]. solve_ndisj.
      iIntros "{$Hcnt} > Hcnt". iPvsIntro.
      iSplitL "Hl Hcnt Hcnt'"; [iExists _; iFrame "Hl Hcnt Hcnt'"; trivial|].
      iExists (♯v _); eauto.
      Unshelve. solve_ndisj.
  Qed.
End CG_Counter.

Theorem counter_ctx_refinement :
  [] ⊨ FG_counter ≤ctx≤ CG_counter :
         TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
Proof.
  set (Σ := #[auth.authGF heapUR; auth.authGF cfgUR]).
  eapply (@binary_soundness Σ);
    auto using FG_counter_closed, CG_counter_closed, FG_CG_counter_refinement.
  all: typeclasses eauto.
Qed.
