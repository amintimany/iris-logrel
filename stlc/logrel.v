From iris.program_logic Require Export weakestpre.
From iris_logrel.stlc Require Export lang typing.

(** interp : is a unary logical relation. *)
Section logrel.
Context {Σ : iFunctor}.

Fixpoint interp (τ : type) (w : val) : iProp lang Σ :=
  match τ with
  | TUnit => w = UnitV
  | TProd τ1 τ2 => ∃ w1 w2, w = PairV w1 w2 ∧ interp τ1 w1 ∧ interp τ2 w2
  | TSum τ1 τ2 =>
     (∃ w1, w = InjLV w1 ∧ interp τ1 w1) ∨ (∃ w2, w = InjRV w2 ∧ interp τ2 w2)
  | TArrow τ1 τ2 =>
     □ ∀ v, interp τ1 v → WP App (of_val w) (of_val v) {{ interp τ2 }}
  end%I.

Global Instance interp_persistent τ v : PersistentP (interp τ v).
Proof. revert v; induction τ=> v /=; apply _. Qed.
End logrel.
