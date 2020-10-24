From LF Require Export Induction.
Module NatList.

  Inductive natprod : Type :=
    | Pair (n1 n2 : nat).

  Check (Pair 1 2).

  Definition fst (n: natprod) :=
    match n with
    | Pair x y => x
    end.

  Compute (fst (Pair 1 2)).

  Definition snd (n: natprod) :=
    match n with
    | Pair x y => y
    end.

  Notation "( x , y )" := (Pair x y).

  Definition swap_pair (n: natprod) :=
    match n with
    | (x, y) => (y, x)
    end.

  Theorem surjective_pair' : forall (n m : nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pair_stuck : forall (p: natprod),
      p = ( fst p, snd p ).
  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      ( snd p, fst p) = swap_pair p.
  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intros p. destruct p as [n m]. simpl. reflexivity.
  Qed.

  (* lists of Numbers *)

  Inductive natList : Type :=
  | nil
  | cons (n : nat) (l : natList).

  Definition myList := cons 1 (cons 2 (cons 3 nil)).

  Check myList.

  Compute myList.

  Notation "x :: l" := (cons x l)
                         (at level 60, right associativity).

  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natList :=
    match count with
    | O => []
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length ( nl : natList ) : nat :=
    match nl with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint append ( l1 l2 : natList ) : natList :=
    match l1 with
    | nil => l2
    | l::l1' => l :: (append l1' l2)
    end.

  Notation "x ++ y" := (append x y) (right associativity, at level 60).

  Fixpoint head (default:nat) (nl : natList) : nat :=
    match nl with
    | nil => default
    | h :: t => h
    end.

  Fixpoint tail ( nl : natList ) : natList :=
    match nl with
    | nil => nil
    | h :: t => t
    end.

  


































End NatList.


