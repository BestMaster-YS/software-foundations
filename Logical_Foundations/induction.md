# Induction 归纳证明

本章节主要讲解核心证明策略：induction

```coq
Theorem plus_n_0_firsttry : forall n:nat,
    n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0*)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite <- IHn'. reflexivity.
Qed.
```

归纳证明策略类似于数学中的归纳法。归纳证明会对对应的变量把本命题分解为两个子命题（subgoal）。现在只是暂时应用到 nat 这种归纳类型上，可以认为是数学归纳法。

在上述例子中，induction n as [| n' IHn']. 把 n = n + 0. 分解为

1：n = O, 直接 simpl. reflexivity 证明.

2:   得到假设：n = n + 0.  证明 S n = S n + 0.

证明加法交换律

```coq
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
```

 加法结合律

```coq
Theorem plus_assoc : forall n m p : nat,
    (n + m) + p = n + (m + p).
Proof.
  intros n m p. induction n as [| n IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
```

## Proofs within Proofs

```coq
Theorem mult_0_plus' : forall n m: nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
                         rewrite -> H.
  reflexivity.
Qed.
```

## 更多练习

```coq

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
```



























