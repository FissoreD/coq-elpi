From elpi.apps.tc Require Import compiler.
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.

Generalizable All Variables.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) :=
  inj x y : S (f x) (f y) -> R x y.

Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.

Elpi Override TC TC_check Only Inj Inj2.

Definition gInj x := x + 1.
Definition fInj x := x * 3.

Axiom eq1 : relation nat.
Axiom eq2 : relation nat.
Axiom eq3 : relation nat.

Local Instance isInjg : Inj eq3 eq1 gInj. Admitted.

Local Instance isInjf : Inj eq1 eq3 fInj. Admitted.

Local Instance isInjf_old : Inj eq1 eq2 fInj. Admitted.
Local Instance isInjg_old : Inj eq2 eq3 gInj. Admitted.

Local Instance isInjf_eq : Inj eq eq fInj. Admitted.
Local Instance isInjg_eq : Inj eq eq gInj. Admitted.

Local Instance id_inj {A} : Inj eq eq (@id A). Admitted.
Local Instance inl_inj {A B} : Inj eq eq (@inl A B). Admitted.
Local Instance inr_inj {A B} : Inj eq eq (@inr A B). Admitted.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f).
Admitted.

Elpi add_instances Inj.

(* TODO : maybe we should solve the exists ? *)
Goal exists A B, Inj A B (compose gInj fInj). Admitted.

Check (_ : Inj _ _ (compose gInj fInj)).

Goal forall (T1 T2 : Type) (f: T1 -> T2), 
  let r := Inj eq eq f in 
  let x := true in
  (if x then r else r) -> Inj eq eq f.
  intros ? ? f r x H.
  unfold x, r in H.
  apply _.
Qed.

Goal forall (T1 T2 : Type) (f: T1 -> T2), 
  let r := Inj eq eq f in 
  let b := true in 
  let cond := (match b with 
    | true => r 
    | false => f = f end) in 
  cond -> Inj eq eq f.
  intros.
  unfold cond in H.
  simpl in H.
  unfold r in H.
  Check (_ : Inj _ _ f).
  apply _.
Qed.

Local Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 ff} y : Inj R1 R3 (λ x, ff x y).
Admitted.

Global Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 ff} x : Inj R2 R3 (ff x).
Admitted.

Elpi add_instances Inj.

Goal Inj2 eq eq eq Nat.mul -> Inj eq eq (Nat.mul 0).
  intros.
  apply _.
Qed.

Goal Inj2 eq eq eq Nat.add -> Inj eq eq (fun x => Nat.add x 0).
intros.
apply _.
Qed.

Definition p (T : Type) := @pair T T.

Goal Inj eq eq (compose fInj gInj).
Proof.
apply _.
Qed.

Elpi Accumulate tc.db lp:{{
  tc {{:gref Inj}} _ {{ Inj lp:R1 lp:R3 lp:F }} S :- 
    F = (fun _ _ _), !,
    G = {{ compose _ _ }},
    coq.unify-eq G F ok,
    tc {{:gref Inj}} _ {{ Inj lp:R1 lp:R3 lp:G }} S.
}}.
Elpi Typecheck TC_check.

Check (_ : Inj _ _ (compose fInj gInj)).
Check (_ : Inj _ _ (fun x => fInj (gInj x))). 

Goal forall (A: Type) (x: A -> A), let y := Inj eq eq x in let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  unfold z, y in H.
  apply _.
Qed. 