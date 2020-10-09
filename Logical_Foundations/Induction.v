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



