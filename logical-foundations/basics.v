Definition pierce := forall (p q : Prop),
  ((p -> q) -> p) -> p.

Definition lem := forall p, p \/ ~ p.

Theorem pierce_equiv_lem: pierce <-> lem.
Proof.
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~ (p \/ ~p )).
  firstorder.
  destruct (H p).
  assumption.
  tauto.

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

(* 用 Compute 指令来计算包含 next_weekday 的复合表达式 *)
Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

(* 我们可以将期望的结果写成 Coq 的示例 *)
Example test_next_weekday:
  (next_weekday(next_weekday saturday)) = tuesday.

(* 经过一番化简后，若等式两边的求值结果相同，该断言即可得证 *)
Proof. simpl. reflexivity. Qed.


Inductive bool: Type :=
  | true
  | false.

Definition negb(b: bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb(b1: bool)(b2: bool): bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb(b1: bool)(b2: bool): bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(*  Notation 指令能为既有的定义赋予新的中缀记法 *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* 特殊的指令 Admitted 被用作不完整证明的占位符 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match (b1, b2) with
  | (false, _) => true
  | (_, false) => true
  | _ => false
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1, b2, b3) with
  | (true, true, true) => true
  | _ => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Check 指令会让 Coq 显示一个表达式的类型 *)
Check true.
Check (negb true).
Check negb.

Inductive rgb: Type :=
  | red
  | green
  | blue.

Inductive color: Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome(c: color): bool :=
  match c with
    | black => true
    | white => true
    | primary q => false
  end.

Definition isread(c: color): bool :=
  match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
  end.


(* Tuple *)
Inductive bit: Type :=
  | B0
  | B1.

Inductive nybble: Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero(nb: nybble): bool := 
  match nb with 
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)


(* Module NatPlayground. *)

(* Inductive nat: Type :=
  | O
  | S (n: nat)
  . *)


Definition pred(n: nat): nat :=
  match n with
    | O => 0
    | S n' => n'
  end.

Check (S (S (S (S 0)))).
(* 4 : nat  *)

Definition minustwo(n: nat): nat := 
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check S.
Check pred.
Check minustwo.

(* End NatPlayground. *)


Fixpoint evenb(n: nat): bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb(n: nat): bool := negb(evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

(* Module Nat2. *)
  Fixpoint plus (n: nat) (m: nat): nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.

  Compute (plus 3 2).

  Fixpoint mult(n m: nat): nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.
  
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m: nat) : nat :=
    match n, m with
      | O , _ => O
      | S _ , O => n
      | S n', S m' => minus n' m'
    end.
(* End Nat2. *)

Fixpoint exp(base power: nat): nat :=
    match power with
      | O => S O
      | S p => mult base (exp base p)
    end.


Fixpoint factorial (n: nat) : nat :=
  match n with
    | O => S O
    | S n' => mult (S n') (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.
