# Coq 初体验

```Coq
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
```

**Inductive** 关键词定义归纳类型

**Definition** 关键词一般定义函数

```Coq
Compute (next_weekday friday).
```

**Compute** 关键词标识进行计算

```Coq
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. Reflexivity. Qed.
```

Example, Lemma, Theorem 等关键词都表示一个意思，声明一个需要证明的命题。

命题的证明的步骤都是在 Proof.  和  Qed. 之间。

simpl. Reflexivity. 等都是Coq 证明的策略（ tactic. ）

simpl. 对等式两边的进行化简并展示化简步骤。

Reflexivity. 对等式两边化简（不展示步骤），并判断等式两边是否相等。

```Coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
```

## Modules

```Coq
Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.
```

Coq 中模块包裹在关键词 Module moduleName.  End moduleName. 之间。

## Tuples

```Coq
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) ⇒ true
    | (bits _ _ _ _) ⇒ false
  end.
```

## Proof by Simplification

```Coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
```

在上述命题中，增加了全称量词 forall n (  $\forall$ n ). 

上述命题表示为对于任意自然数 n, 0 + n = n. 

**intros.** 关键词将把量词 n 转移到当前证明的上下文中.

## Proof by Rewriting

```Coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.
```

上述代码中，plus_id_example 这个命题引入两个全称量词 n, m, 并且引入 n = m 作为前提条件，要证明的结论是  n + n = m + m，证明中 intros 先引入 n, m,  再用 intros 引入 n = m 这个前提条件，rewrite 的含义是用先用的等式，把证明目标中的对应的进行替换，$\leftarrow$ 表示右边的表达式替换为左边的表达式，要证明的结论就成为 n + n = m + m, $\rightarrow$ 则相反。

```Coq
Lemma mult_n_0: forall n: nat,
    0 = n * 0.
Proof. Admitted.

Lemma mult_n_Sm: forall n m : nat,
    n * m + n = n * S m.
Proof. Admitted.

Theorem mult_n_1: forall n : nat,
    n * 1 = n.
Proof.
  intros.
  rewrite <- (mult_n_Sm n 0).
  (* n * 0 + n = n * 1 *)
  (* n * 0 + n = n  *)
  rewrite <- (mult_n_0 n).
  reflexivity.
Qed.
```

上述代码中，引理 mult_n_0，mult_n_Sm 先使用 Admitted 略过证明，直接拿来证明理论 mult_n_1 。

intros 不写变量表示引入全部的。

## Proof by Case Analysis

```Coq
Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```

**destruct** 可以对归纳类型进行分解，因为 nat 含有两个构造子，则分成两个子目标分开证明，"as [| n']" 为 intro pattern. 显示子目标构造子参数变量名称，由 | 进行分隔。由于 O构造子没有参数，则不显示。在每个子目标中 Coq 会记住此目标中 n 为 O 或者 S n'。"eqn:E" The eqn:E annotation tells destruct to give the name E to this equation. Leaving off the eqn:E annotation causes Coq to elide these assumptions in the subgoals. 

```Coq
Theorem negb_involution : forall b : bool,
	negb (negb) = b.
Proof.
	intros b.
	destruct b eqn:E.
	- reflexivity.
	- reflexivity.
Qed.

(*
当coq运行至 destruct b eqn:E. 时
  b : bool
  E : b = true
  ============================
  negb (negb true) = true
*)
```

在证明 negb_involution 中，E 代表等式 b = true.

```Coq

Theorem andb_commutative : ∀ b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```

\- 和 \+ 表示对改命题分情况讨论，并且可以无限的进行细分。也可以采用不用的符号。

### 练习

```
(* 不知道是不是正确答案，但是能通过coq证明 *)
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
```

```Coq
intros b c. destruct b as [|b'] eqn:E.

(* 简化为 *)

intros [|b'] [].
```

```
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
```

at level 40  代表优先级，left associativity 代表左结合。

## 更多练习

```Coq

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
```

