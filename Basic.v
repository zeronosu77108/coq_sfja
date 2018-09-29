Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.


Proof.
    simpl.
    reflexivity.
Qed.



Inductive bool : Type :=
    | true : bool
    | false : bool.

Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T. Admitted.


Definition nandb (b1:bool) (b2:bool) : bool :=
    negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof.  simpl.  reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof.  simpl.  reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof.  simpl.  reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof.  simpl.  reflexivity. Qed.

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n:nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Playground1.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check minustwo.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
    match beq_nat n m with
    | false => false
    | true => negb (ble_nat n m)
    end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. compute. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. compute. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. compute. reflexivity. Qed.


Theorem plus_O_n : forall n:nat, O + n = n.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.


Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
   intros n m. 
   intros H.
   rewrite -> H.
   reflexivity.
Qed.


Theorem plus_id_exercise : forall n m o :nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros.
    rewrite <- H.
    rewrite -> H0.
    reflexivity.
Qed.


Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
    intros.
    rewrite -> plus_O_n.
    reflexivity.
Qed.


Theorem mult_1_plus : forall n m : nat,
    (1 + n) * m = m + (n * m).
Proof.
    intros.
    reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
    intros.
    destruct n as [_| n'].
    reflexivity.
    reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
    intros.
    destruct b as [].
    reflexivity.
    reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
    intros.
    destruct n as [|n'].
    reflexivity.
    reflexivity.
Qed.


Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
    intros.
    destruct b.
    Case "b = ture".
        reflexivity.
    Case "b = false".
        rewrite <- H.
        reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros.
    destruct c.
    Case "c = true".
        reflexivity.
    Case "c = false".
        rewrite <- H.
        destruct b.
        SCase "b = true".
            reflexivity.
        SCase "b = false".
            reflexivity.
Qed.


Theorem plus_0_r: forall n:nat,
  n + 0 = n.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0". reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
    intros.
    induction n as [_|n'].
    (* n = 0 *)
        reflexivity.
    (* n = S n' *)
        simpl. 
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
    intros.
    induction n as [_|n'].
    (* n = 0 *)
        reflexivity.
    (* n = S n' *)
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.


Theorem plus_n_Sm : forall n m :nat,
    S (n + m) = n + (S m).
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        rewrite -> plus_0_r.
        reflexivity.
    Case "n = S n'".
        induction m as [_|m'].
        SCase "m = 0".
            simpl.
            rewrite -> plus_0_r.
            reflexivity.
        SCase "m = S m'".
            simpl.
            rewrite -> IHn'.
            rewrite <- plus_n_Sm.
            simpl.
            reflexivity.
Qed.



Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus : forall n,
    double n = n + n.
Proof.
    intros.
    induction n as [_| n'].
    (* n = 0 *)
        simpl.
        reflexivity.
    (* n = S n' *)
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat,
    true = beq_nat n n.
Proof.
    intros.
    induction n as [_| n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite <- IHn'.
        reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.


    
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (0 + n = n) as H.
    Case "Proof of assertion".
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
    intros.
    rewrite -> plus_assoc.
    assert (n + m = m + n).
        rewrite -> plus_comm.
        reflexivity.
    rewrite -> H.
    rewrite <- plus_assoc.
    reflexivity.
Qed.


Theorem mult_1_r : forall n:nat,
    n * 1 = n.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.



Theorem mul_comm : forall a b, a * b = b * a.
Proof.
  induction a.
  (* Case Z *)
    induction b.
      (* Case Z *)   reflexivity.
      (* Case S b *) simpl. rewrite <- IHb. reflexivity.
  (* Case S a *)
    induction b.
      (* Case Z *)
        simpl. rewrite (IHa 0). reflexivity.
      (* Case S b *)
        simpl. rewrite <- IHb.
        rewrite (IHa (S b)).
        simpl. rewrite (IHa b).
        rewrite (plus_assoc b a (b * a)).
        rewrite (plus_assoc a b (b * a)).
        rewrite (plus_comm a b).
        reflexivity.
Qed.





Lemma _mult_comm : forall n m : nat,
    m + m * n = m * S n.
Proof.
    intros.
    induction m as [_|m'].
    Case "m = 0".
        simpl.
        reflexivity.
    Case "m = S m'".
        simpl.
        rewrite <- IHm'.
        rewrite -> plus_swap.
        reflexivity.
Qed.
        

Theorem mult_comm : forall n m : nat,
    n * m = m * n.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        rewrite -> mult_0_r.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        induction m as [_|m'].
        SCase "m = 0".
            simpl.
            reflexivity.
        SCase "m = S m'".
            simpl.
            rewrite -> plus_swap.
            assert (m' + m' * n' = m' * S n').
            (* Subgoals appear indefinitely. *)
            (* It can't proof here. *)
                rewrite -> _mult_comm.
                reflexivity.
            rewrite -> H.
            reflexivity.
Qed.



(* Exercise *)
Theorem evenb_n__oddb_Sn : forall n : nat,
    evenb n = negb (evenb (S n)).
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        rewrite -> negb_involutive.
        reflexivity.
Qed.


Theorem ble_nat_refl : forall n:nat,
    true = ble_nat n n.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.


Theorem zero_nbeq_S : forall n:nat,
    beq_nat 0 (S n) = false.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Theorem andb_false_r : forall b:bool,
    andb b false = false.
Proof.
    intros.
    destruct b.
    Case "b = true".
        simpl.
        reflexivity.
    Case "b = false".
        simpl.
        reflexivity.
Qed.


Theorem plus_ble_compat_l : forall n m p : nat,
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
    intros.
    rewrite <- H.
    induction p as [_|p'].
    Case "p = 0".
        simpl.
        reflexivity.
    Case "p = S p'".
        simpl.
        rewrite -> IHp'.
        reflexivity.
Qed.


Theorem S_nbeq_0 : forall n:nat,
    beq_nat (S n) 0 = false.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Theorem mult_1_l : forall n:nat,
    1 * n = n.
Proof.
    intros.
    simpl.
    rewrite -> plus_0_r.
    reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb (andb b c)
        (orb (negb b)
             (negb c))
    = true.
Proof.
    intros.
    destruct b.
    Case "b = true".
        simpl.
        destruct c.
        SCase "c = true".
            simpl.
            reflexivity.
        SCase "c = false".
            simpl.
            reflexivity.
    Case "b = false".
        simpl.
        reflexivity.
Qed.


Theorem mult_plus_distor_r : forall n m p :nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_assoc.
        reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
    intros.
    induction n as [_|n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        rewrite -> mult_plus_distor_r.
        reflexivity.
Qed.

