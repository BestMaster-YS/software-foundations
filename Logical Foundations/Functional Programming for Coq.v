Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

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


Compute (next_weekday friday).


Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | false => b2
  | true => true
  end.



Example test_orb1:
  (orb true false) = true.

Proof. simpl. reflexivity. Qed.


Theorem t_and_t_eq_t: (andb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_and1:
  (true && true) = true.
Proof.
  simpl.
  reflexivity.
Qed.


(* exercise nand  *)
Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => match b2 with
            | false => true
            | true => false
            end
  | false => match b2 with
             | false => true
             | true => true
             end
  end.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise  *)
Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb3: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


Example test_andb3_2: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

(* Types *)

Check true.
Check negb.

(* new Type from old *)

Inductive rgb : Type :=
| red
| green
| blue.

Check andb3.

Inductive color : Type :=
| black
| white
| primary (p: rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.


(* 模块 *)

Module Test.
  Inductive testType : Type :=
  | noTest
  | test.
End Test.

Definition testA: Test.testType := Test.noTest.

(* Tuple *)

Inductive bit : Type :=
| B0
| B1.

Inductive nybble: Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0) : nybble.

Definition all_zero (ny1: nybble) : bool :=
  match ny1 with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.


Compute (all_zero (bits B1 B0 B0 B1)).

(* Natrual Numbers *)

Module NatPlayround.

  Inductive nat : Type :=
  | O : nat
  | S (n : nat) : nat.

  Definition pred (n: nat) :=
    match n with
    | O => O
    | S n' => n'
    end.

End NatPlayround.

Check (S (S (S (S O)))).

Definition minusTwo (n: nat) :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minusTwo 5).

Check S.
Check pred.
Check minusTwo.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Compute (evenb 5).

Definition oddn (n:nat) :bool :=
  negb (evenb n).

Compute (oddn 5).

Module NatPlayround2.

  Fixpoint plus (n: nat) (m: nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Compute (plus 3 5).

  Fixpoint mult (n m: nat) : nat :=
    match n with
    | O => O
    | S O => m
    | S (S n') => plus (plus m m) (mult n' m)
    end.

  Example test_mult_3_3_equal_9: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

  Example test_minus1: (minus 3 2) = 1.
  Proof. simpl. reflexivity. Qed.

End NatPlayround2.

Fixpoint exp (base power: nat) : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.


Compute (exp 2 3).

(* Exercise factorial *)
Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.


Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Check ((0 + 1) + 1) : nat.

Compute ((0 + 1) + 1).

(* equal number  *)

Fixpoint eqb (n m: nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: leb 1 2 = true .
Proof. simpl. reflexivity. Qed.

Example test_eqb1: eqb 1 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb2: eqb 2 2 = true.
Proof. simpl. reflexivity. Qed.


Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3: (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


(* exercise *)
Fixpoint ltb (n m: nat) : bool :=
  match n,m with
  | O, O => false
  | O, S m' => true
  | S n',O => false
  | S n', S m' => ltb n' m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 3) = true.
Proof. simpl. reflexivity. Qed.

(* Proof by simplification *)


Theorem plus_0_n : forall n: nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_1 : forall n: nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_1 : forall n: nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Proof by rewriting *)


Theorem plus_id: forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* plus_id exercise  *)

Theorem plus_id_exercise: forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.


(*
Check mult_0_1.
乘法定义中 0 * n = 0，不能直接得到 n * 0 = 0.
*)
Theorem mult_n_0_m_0 : forall p q : nat,
    (0 * p) + (0 * q) = 0.
Proof.
  intros q p.
  rewrite -> (mult_0_1 q).
  rewrite -> (mult_0_1 p).
  reflexivity. Qed.


Check mult.

(* exercise 先将下列两个lemma作为已知条件 *)

Lemma mult_n_0: forall n: nat,
    0 = n * 0.
Proof. Admitted.

Lemma mult_n_Sm: forall n m : nat,
    n * m + n = n * S m.
Proof. Admitted.


Theorem mult_n_1: forall n : nat,
    n * 1 = n.
Proof.
  intros n.
  rewrite <- (mult_n_Sm n 0).
  (* n * 0 + n = n * 1 *)
  (* n * 0 + n = n  *)
  rewrite <- (mult_n_0 n).
  reflexivity.
Qed.

(* Proof by case analysis *)

Theorem plus_1_equal_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall a b, andb a b = andb b a.
Proof.
  intros c b. destruct b eqn:Eb.
  {
    destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. }
  }
  {
    destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. }
  }
Qed.


(* Exercise *)

Theorem andb_true_clim2: forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  (* b = true *)
  - destruct c eqn:Ec.
    (* c = true *)
    + reflexivity.
    (* c = false *)
    + intros H.
      rewrite <- H.
      reflexivity.
  (* b = false *)
  - destruct c eqn:Ec.
    (* c = true *)
    + reflexivity.
    (* c = false *)
    + intros H.
      rewrite <- H.
      reflexivity.
Qed.



Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint plus' (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.


(* 练习 2**  *)

(*
Definition plus_without_fixpoint (n: nat) (m: nat) :nat :=
  match n with
  | O => m
  | S n' => S (plus_without_fixpoint n' m)
  end.

Error: The reference plus_without_fixpoint was not found
in the current environment.

*)

(* more exercise *)

Theorem identity_fn_applied_twice : forall (f: bool -> bool),
    (forall (a : bool), f a = a) ->
    forall (b: bool), f (f b) = b.
Proof.
  intros f. intros H.
  intros [].
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice : forall (f: bool -> bool),
    (forall (a: bool), f a = negb a) ->
    forall (b: bool), f (f b) = b.
Proof.
  intros f. intros H.
  intros [].
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

(* 先证明四个引理 *)

Lemma and_true_eq_another: forall b: bool,
    andb true b = b.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Lemma or_false_eq_another: forall b: bool,
    orb false b = b.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c: bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - rewrite -> (and_true_eq_another c).
    intros H.
    rewrite -> H.
    reflexivity.
  - rewrite -> (or_false_eq_another c).
    (* false && c = c -> false = c *)
    intros H.
    (*
      H: false && c = c
      false = c
    *)
    rewrite <- H.
    reflexivity.
Qed.

Inductive bin : Type :=
| Z
| Bin0 (n: bin)
| Bin1 (n: bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z => Bin1 Z
  | Bin0 m' => Bin1 m'
  (* 增加一位 Bin0, 自身的Bin1变为Bin0 *)
  (* 分两种情况，Bin1 Z 不能把 Bin1 变为 Bin0 *)
  | Bin1 Z => Bin0 (Bin1 Z)
  | Bin1 m' => Bin0 (Bin0 m')
  end.


(* bin 转化为 nat *)

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => O
  | Bin0 m' => NatPlayround2.mult (bin_to_nat m') 2
  | Bin1 m' => S (NatPlayround2.mult (bin_to_nat m') 2)
  end.


Compute (bin_to_nat (Bin1 Z)).

Compute (bin_to_nat (Bin0 (Bin1 Z))).

Compute (bin_to_nat (Bin1 (Bin0 (Bin1 Z)))).

Example test_bin_incr1: (incr (Bin1 Z)) = Bin0 (Bin1 Z).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr2 : (incr (Bin0 (Bin1 Z))) = Bin1 (Bin1 Z).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr3 : (incr (Bin1 (Bin1 Z))) = Bin0 (Bin0 (Bin1 Z)).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (Bin0 (Bin1 Z)) = 2.
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (Bin1 Z)) = 1 + bin_to_nat (Bin1 Z).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (Bin1 Z))) = 2 + bin_to_nat (Bin1 Z).
Proof.
  simpl. reflexivity.
Qed.


