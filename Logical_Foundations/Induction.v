From LF Require Export Basics.

Theorem plus_n_0_firsttry : forall n:nat,
    n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0*)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite <- IHn'. reflexivity.
Qed.

(*Exercise*)

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n * 0 = 0 -> S n * 0 = 0 *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

(* 加法交换律 *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction m as [| m' IHm'].
  - rewrite <- (plus_n_0_firsttry n). reflexivity.
  - simpl. rewrite <- IHm'. rewrite -> (plus_n_Sm n m'). reflexivity.
Qed.


(*加法结合律*)
Theorem plus_assoc : forall n m p : nat,
    (n + m) + p = n + (m + p).
Proof.
  intros n m p. induction n as [| n IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n: nat,
    double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- plus_comm. simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> (negb_involutive (evenb n')).
    reflexivity.
Qed.

(*proofs within proofs*)

Theorem mult_0_plus' : forall n m: nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
                         rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q: nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> (plus_comm n m).
  reflexivity.
Qed.


(*更多练习*)

Theorem plus_swap : forall n m p: nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> (plus_comm n p).
  rewrite -> (plus_comm n (m + p)).
  rewrite <- (plus_assoc m p n).
  reflexivity.
Qed.

(*乘法交换律*)

Lemma mult_0_eq_0 : forall n: nat,
    0 = n * 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma mult_plus_1 : forall n m : nat,
    m * n + m = m * S n.
Proof.
  intros n m. induction m as [| m' IHm'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHm'.
    rewrite <- (plus_assoc n (m' * n) m').
    rewrite <- (plus_n_Sm (n + m' * n) m').
    reflexivity.
Qed.

Theorem mult_comm : forall n m: nat,
    n * m = m * n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- (mult_0_eq_0 m). reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> (plus_comm m (m * n')).
    rewrite <- (mult_plus_1 n' m). reflexivity.
Qed.


(*练习*)

Theorem leb_refl : forall n: nat,
    true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem zero_nbeq_S : forall n : nat,
    0 =? (S n) = false.
Proof.
  intros n. destruct n as [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b: bool,
    andb b false = false.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem plus_ble_compat_l : forall n m p: nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. intros H. induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.


(*乘法结合律*)

Theorem mult_plus_distr_r : forall n m p: nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [| p' IHp'].
  - simpl. rewrite -> (mult_0_r n). rewrite -> (mult_0_r m). rewrite -> (mult_0_r (n + m)). reflexivity.
  - rewrite <- (mult_plus_1 p' (n + m)).
    rewrite <- (mult_plus_1 p' n).
    rewrite <- (mult_plus_1 p' m).
    rewrite -> IHp'.
    rewrite -> (plus_assoc (n * p')  (m * p') (n + m)).
    rewrite -> (plus_assoc (n * p')  n (m * p' + m)).
    rewrite -> (plus_comm (n * p') (m * p' + (n + m))).
    rewrite -> (plus_comm (n * p') (n + (m * p' + m))).
    rewrite -> (plus_swap n (m * p') m).
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> (mult_plus_distr_r m (n' * m) p).
    reflexivity.
Qed.

Theorem eqb_refl : forall n: nat,
    true = (n <=? n).
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.


Theorem plus_swap' : forall n m p: nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
Admitted.





