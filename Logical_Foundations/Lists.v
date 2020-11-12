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

  Fixpoint nonzeros (list: natList) : natList :=
    match list with
    | nil => nil
    | h :: t => match h with
                | O => nonzeros t
                | _ => h :: (nonzeros t)
                end
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. simpl. reflexivity. Qed.

  Compute (nonzeros [0;1;0;2;3;0;0]).

  Fixpoint oddermember (list : natList) : natList :=
    match list with
    | nil => nil
    | h :: t => match (oddn h) with
                | false => oddermember t
                | true => h :: (oddermember t)
                end
    end.

  Compute (oddermember [1;2;3;4;5;6]).

  Fixpoint countOddermember (list : natList) : nat :=
    match list with
    | nil => O
    | h :: t => match (oddn h) with
                | false => countOddermember t
                | true => S (countOddermember t)
                end
    end.

  Compute (countOddermember [1;2;3;4;5;6;7;8]).

  Fixpoint alternate (list1 list2 : natList) : natList :=
    match list1 with
    | nil => list2
    | h1 :: t1 => match list2 with
                  | nil => list1
                  | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
                  end
    end.

  Compute (alternate [1;2;3] [4;5;6]).
  Compute (alternate [1] [4;5;6]).
  Compute (alternate [1;2;3] [4]).
  Compute (alternate [] [4;5;6]).

  (*
  Fixpoint merge (list1 list2 : natList) : natList :=
    match list1 with
    | nil => list2
    | h :: t => h :: (merge list2 t)
    end.
   *)

  (* Bags via lists *)

  Definition bag := natList.

  Fixpoint count (v: nat) (b: bag) : nat :=
    match b with
    | nil => O
    | h :: t => if h =? v then (count v t) + 1 else count v t
    end.

  Compute (count 1 [1;2;1;3;1;4]).
  Compute (count 6 [1;2;3;4;5;6]).

  Definition sum : bag -> bag -> bag := append.
  Compute (count 1 (sum [1;2;3] [1;3;1])).

  Definition add (v : nat) (s : bag) : bag := v :: s.
  Compute (count 1 (add 1 [1;3;1])).

  Definition member (v : nat) (s : bag) : bool :=
    negb ((count v s) =? 0).

  Compute (member 1 [1;2]).
  Compute (member 2 [1;3;4]).

  Fixpoint remove_one (v: nat) (s: bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if v =? h then t else h :: (remove_one v t)
    end.


  Compute (count 4 (remove_one 5 [2;1;4;5;1;4])).
  Compute (count 5 (remove_one 5 [2;1;5;4;5;1;4])).

  Fixpoint remove_all (v: nat) (s: bag) : bag :=
    match s with
    | nil => nil
    | h :: t => if v =? h then remove_all v t else h :: (remove_all v t)
    end.
  Compute (count 4 (remove_all 5 [2;1;4;5;1;4])).
  Compute (count 5 (remove_all 5 [2;1;5;4;5;1;4])).

  Fixpoint subset (s1: bag) (s2: bag) : bool :=
    match s1 with
    | nil => true
    | h :: t => if member h s2 then subset t (remove_one h s2) else false
    end.

  Compute (subset [1;2] [2;1;4;1]).
  Compute (subset [1;2;2] [2;1;4;1]).

  Theorem add_eq_incr_count : forall (list : bag) (a: nat),
      count a (add a list) = S (count a list).
  Proof.
    intros list a.
    assert ( H:  a =? a = true ).
    {
      induction a.
      + reflexivity.
      + simpl. rewrite -> IHa. reflexivity.
    }
    induction list.
    - simpl.
      rewrite -> H. reflexivity.
    - simpl. rewrite -> H.
      assert (H2: forall (n1: nat), n1 + 1 = S n1 ).
      {
        induction n1.
        - reflexivity.
        - simpl. rewrite -> IHn1. reflexivity.
      }
      rewrite -> H2. reflexivity.
  Qed.

  Theorem nil_app : forall l:natList,
      [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem pred_length_tail : forall l:natList,
      pred (length l) = length (tail l).
  Proof.
    intros. destruct l as [| n l'].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natList,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  (*
    右结合: 连续同一优先级的运算符，右边先运算
    左结合: 相反
   *)

  Fixpoint rev_list (l: natList) : natList :=
    match l with
    | nil => nil
    | h :: t => rev_list t ++ [h]
    end.

  Compute (rev_list [1;2;3]).

  Theorem app_length : forall l1 l2: natList,
      length (append l1 l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  Theorem rev_length_firsttry : forall l: natList,
      length l = length (rev_list l).
  Proof.
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length. rewrite -> IHl'.
      simpl. rewrite -> plus_1_eq_S. reflexivity.
  Qed.

  (*练习*)
  Theorem app_nil_r : forall l: natList,
      l ++ [] = l.
  Proof.
    intros l. induction l as [| n' l' IHl'].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_app_distr: forall l1 l2: natList,
      rev_list (l1 ++ l2) = rev_list l2 ++ rev_list l1.
  Proof.
    intros l1 l2. induction l1 as [| n1' l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
  Qed.

  Theorem rev_involutive : forall l: natList,
      rev_list (rev_list l) = l.
  Proof.
    intros l. induction l as [| n' l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity.
  Qed.


  Theorem app_assoc4: forall l1 l2 l3 l4 :natList,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4. rewrite -> app_assoc. rewrite -> app_assoc. reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natList,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [| n1' l1' IHl1'].
    - simpl. reflexivity.
    - destruct n1'.
      + simpl. rewrite -> IHl1'. reflexivity.
      + simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  Fixpoint eqblist (l1 l2: natList) : bool :=
    match l1,l2 with
    | nil, nil => true
    | _, nil => false
    | nil, _ => false
    | h1::t1, h2::t2 => if h1 =? h2 then eqblist t1 t2 else false
    end.

  Theorem eqblist_refl : forall l:natList,
      true = eqblist l l.
  Proof.
    intros l. induction l.
    - reflexivity.
    - simpl. assert (H: true = (n =? n)).
      { induction n.
        - reflexivity.
        - simpl. rewrite -> IHn. reflexivity.
      }
      rewrite <- H. rewrite <- IHl. reflexivity.
  Qed.

  Theorem count_member_nonzero : forall l:natList,
      1 <=? (count 1 (1 :: l)) = true.
  Proof.
    intros l. destruct l.
    - simpl. reflexivity.
    - simpl. rewrite -> plus_1_eq_S. reflexivity.
  Qed.

  Theorem leb_n_Sn : forall n:nat,
      n <=? (S n) = true.
  Proof.
    intros. induction n.
    - reflexivity.
    - simpl. rewrite -> IHn. reflexivity.
  Qed.

  Theorem remove_dose_not_increase_count : forall l:natList,
      (count 0 (remove_one 0 l)) <=? (count 0 l) = true.
  Proof.
    intros. induction l.
    - simpl. reflexivity.
    - simpl. destruct n.
      + simpl. rewrite -> plus_1_eq_S. rewrite -> leb_n_Sn. reflexivity.
      + simpl. rewrite -> IHl. reflexivity.
  Qed.

  (*rev_list 是单射函数*)
  Theorem rev_list_injective : forall (l1 l2 : natList),
      rev_list l1 = rev_list l2 -> l1 = l2.
  Proof.
    (* 妙啊 *)
    intros l1 l2 H. rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
  Qed.

  Inductive natOption : Type :=
  | Some (n: nat)
  | None.

  Fixpoint nth_error (l: natList) (n: nat) :=
    match l with
    | nil => None
    | a :: l' => match n with
                 | O => Some a
                 | S n' => nth_error l' n'
                 end
    end.

  Compute (nth_error [1;2;3;4;5;6] 7).
  Compute (nth_error [1;2;3;4;5;6] 5).


  Definition option_elim (d: nat) (o: natOption) : nat :=
    match o with
    | Some n => n
    | None => d
    end.

  Definition hd_error (l: natList) : natOption :=
    match l with
    | nil => None
    | h::t => Some h
    end.


  Theorem option_elim_hd : forall (l: natList) (default: nat),
      head default l = option_elim default (hd_error l).
  Proof.
    intros l default. destruct l.
    - simpl. destruct default.
      + reflexivity.
      + reflexivity.
    - simpl. destruct default.
      + reflexivity.
      + reflexivity.
  Qed.

  (* partial maps *)
  Inductive id : Type :=
  | Id (n : nat).


  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

  Theorem eq_refl : forall n : nat,
      true = (n =? n).
  Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite -> IHn. reflexivity.
  Qed.

  Theorem eqb_id_refl : forall x : id, true = eqb_id x x.
  Proof.
    intros x. destruct x as [n]. simpl. rewrite <- eq_refl. reflexivity.
  Qed.

End NatList.

Module PartialMap.

  Export NatList.

  Inductive partial_map : Type :=
  | empty
  | record (i: id) (v : nat) (m : partial_map).

  Definition update (d: partial_map) (x: id) (value: nat) : partial_map :=
    record x value d.

  Fixpoint find (x: id) (d: partial_map) : natOption :=
    match d with
    | empty => None
    | record y v d' => if eqb_id x y
                       then Some v
                       else find x d'
    end.

  Theorem update_eq : forall (d: partial_map) (x: id) (v: nat),
      find x (update d x v) = Some v.
  Proof.
    intros. simpl. rewrite <- eqb_id_refl. reflexivity.
  Qed.

  Theorem update_neq: forall (d: partial_map) (x y: id) (o: nat),
      eqb_id x y = false -> find x (update d y 0) = find x d.
  Proof.
    intros. simpl. rewrite -> H. reflexivity.
  Qed.

End PartialMap.

Inductive baz: Type :=
| Baz1 (x: baz)
| Baz2 (y: baz) (b: bool).


(* 两种，Baz1 和 Baz2 两个构造子 *)


