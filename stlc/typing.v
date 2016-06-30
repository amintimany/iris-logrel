From iris_logrel.stlc Require Export lang.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type.

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → typed Γ (Var x) τ
  | Unit_typed : typed Γ Unit TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     typed Γ e1 τ1 → typed Γ e2 τ2 → typed Γ (Pair e1 e2) (TProd τ1 τ2)
  | Fst_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Fst e) τ1
  | Snd_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Snd e) τ2
  | InjL_typed e τ1 τ2 : typed Γ e τ1 → typed Γ (InjL e) (TSum τ1 τ2)
  | InjR_typed e τ1 τ2 : typed Γ e τ2 → typed Γ (InjR e) (TSum τ1 τ2)
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     typed Γ e0 (TSum τ1 τ2) →
     typed (τ1 :: Γ) e1 ρ → typed (τ2 :: Γ) e2 ρ →
     typed Γ (Case e0 e1 e2) ρ
  | Lam_typed e τ1 τ2 :
     typed (τ1 :: Γ) e τ2 → typed Γ (Lam e) (TArrow τ1 τ2)
  | App_typed e1 e2 τ1 τ2 :
     typed Γ e1 (TArrow τ1 τ2) → typed Γ e2 τ1 → typed Γ (App e1 e2) τ2.