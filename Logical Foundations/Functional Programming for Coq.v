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
















