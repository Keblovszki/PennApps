(* Name: Hannibal Krabbe-keblovszki
 * Student number: 20102295
 * Project for introduction to functional programming
 *
 * termproject: Something about fibonacci numbers.
 * Filename: mainProject.v
 *)

Require Import Arith.

(*
 * "The most beautiful thing we can experience is the mysterious. 
 * It is the source of all true art and science." by Albert Einstein
 *)

Definition specification_of_fibonacci (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  fib 2 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Fixpoint fibo (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fibo n' + fibo n''
              end
  end.

Lemma unfold_fib_bc0 :
  fibo 0 = 0.
Proof.
  unfold fibo.
  reflexivity.
Qed.

Lemma unfold_fib_bc1 :
  fibo 1 = 1.
Proof.
  unfold fibo.
  reflexivity.
Qed.

Lemma unfold_fib_bc2 :
  fibo 2 = 1.
Proof.
  unfold fibo.
  reflexivity.
Qed.

Lemma unfold_fib_ic :
  forall n : nat,
    fibo (S (S n)) = fibo (S n) + fibo n.
Proof.
  intro n.
  unfold fibo; fold fibo.
  reflexivity.
Qed.

Theorem there_is_only_one_fibonacci :
  forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci fib1 ->
    specification_of_fibonacci fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  intros H_spec_fib1 H_spec_fib2.

  unfold specification_of_fibonacci in H_spec_fib1.
  destruct H_spec_fib1 as [H_fib1_bc0 [H_fib1_bc1 [H_fib1_bc2 H_fib1_ic]]].

  unfold specification_of_fibonacci in H_spec_fib2.
  destruct H_spec_fib2 as [H_fib2_bc0 [H_fib2_bc1 [H_fib2_bc2 H_fib2_ic]]].

  assert (H_fib : forall m : nat,
                    fib1 m = fib2 m /\ fib1 (S m) = fib2 (S m)).
    intro m.
    induction m as [ | n' [IHn' IHSn']].

    split.

      rewrite -> H_fib1_bc0.
      rewrite -> H_fib2_bc0.
      reflexivity.
      
      rewrite -> H_fib1_bc1.
      rewrite -> H_fib2_bc1.
      reflexivity.
      
    split.
    
      rewrite -> IHSn'.
      reflexivity.

      rewrite -> H_fib2_ic.
      rewrite <- IHSn'.
      rewrite <- IHn'.
      rewrite -> H_fib1_ic.
      reflexivity.

  intro n.
  destruct (H_fib n) as [H_fib_n _].
  rewrite -> H_fib_n.
  reflexivity.
Qed.

Proposition about_fib_of_a_sum :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall p q : nat,
      fib (S (p + q)) = fib (S p) * fib (S q) + fib p * fib q.
Proof.
  intro fib.
  intro H_spec.
  intros p.

  unfold specification_of_fibonacci in H_spec.
  destruct H_spec as [H_bc0 [H_bc1 [H_bc2 H_ic]]].

  induction p as [ | p' IHp'].

  intro q.
  rewrite -> plus_0_l.
  rewrite -> H_bc1.
  rewrite -> H_bc0.
  rewrite -> mult_0_l.
  rewrite -> mult_1_l.
  rewrite -> plus_0_r.
  reflexivity.

  intro q.
  rewrite -> H_ic.
  rewrite -> mult_plus_distr_r.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm ((fib p') * (fib (S q))) (fib (S p') * fib q)).  
  rewrite -> plus_Snm_nSm.
  rewrite -> IHp'.
  rewrite -> H_ic.
  rewrite -> mult_plus_distr_l.
  rewrite <- plus_assoc.
  reflexivity.
Qed.

(*
 * Compute
 *   let foo p q := (fibo (S (p + q)),
 *                   fibo (S p) * fibo (S q) + fibo p * fibo q)
 *   in foo 4 6.
 *      = (89, 89)
 *      : nat * nat
 *)

Proposition d_Occagne_s_identity :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib ((S n) + (S n)) = fib (S n) * (fib (S (S n)) + fib n).
Proof.
  intro fib.
  intro H_spec_fib.
  intro n.

  rewrite -> mult_plus_distr_l.
  rewrite -> mult_comm.

  (*
   * God lends a helping hand to the man who tries hard.
   * by Aeschylus
   *)

  rewrite <- (about_fib_of_a_sum _ H_spec_fib _).
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

(*
 * Compute
 *   let foo n := (fibo ((S n) + (S n)), fibo (S n) * (fibo (S (S n)) + fibo n))
 *   in foo 4.
 * = (55, 55)
 * : nat * nat
 *)

Definition square (x : nat) : nat :=
  x * x.

Lemma unfold_square :
  forall x : nat,
    square x = x * x.
Proof.
  intro x.
  unfold square.
  reflexivity.
Qed.

(*
 * This next quote holds for both Cassinis identity for even numbers
 * and for Cassinis identity for odd numbers (: 
 * 
 * "If you're walking down the right path and you're willing to keep 
 * walking, eventually you'll make progress." by Barack Obama.
 *)

Proposition Cassini_s_identity_for_even_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      square (fib (S (n + n))) =
      S ((fib ((S n) + (S n))) * (fib (n + n))).
Proof.
  intro fib.
  intro H_spec_fib.
  intro n.

  unfold specification_of_fibonacci in H_spec_fib.
  destruct H_spec_fib as [H_fib_bc0 [H_fib_bc1 [H_fib_bc2 H_fib_ic]]].

  induction n as [ | n' IHn'].

  rewrite -> plus_0_r.
  rewrite -> H_fib_bc1.
  rewrite -> unfold_square.
  rewrite -> mult_1_r.
  rewrite -> H_fib_bc0.
  rewrite -> mult_0_r.
  reflexivity.

  rewrite -> unfold_square.
  rewrite -> plus_Sn_m at 2.
  rewrite -> H_fib_ic.
  rewrite -> mult_plus_distr_l.
  rewrite -> plus_Sn_m at 2.
  rewrite -> H_fib_ic.
  rewrite -> mult_plus_distr_r.
  rewrite <- unfold_square.
  rewrite <- (plus_n_Sm n' n') at 4.
  rewrite -> IHn'.
  rewrite -> plus_assoc.
  rewrite <- plus_n_Sm.
  rewrite -> plus_Sn_m at 2.
  rewrite -> plus_comm.
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  rewrite -> plus_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite <- plus_n_Sm at 2.
  rewrite <- H_fib_ic.
  rewrite -> mult_comm.
  rewrite <- mult_plus_distr_r.
  rewrite -> plus_comm.
  rewrite -> plus_Sn_m at 1.
  rewrite <- plus_n_Sm at 1.
  rewrite <- H_fib_ic.
  rewrite <- (plus_Sn_m n' (S n')).
  rewrite ->2 plus_n_Sm.
  rewrite <-2 plus_Sn_m.
  reflexivity.
Qed.

Compute 
  let foo n :=       
      (square (fibo (S (n + n))),
       S ((fibo ((S n) + (S n))) * (fibo (n + n))))
  in foo 2.

(*
 * Compute
 *   let foo n :=
 *       (square (fibo (S (n + n))),
 *        S ((fibo ((S n) + (S n))) * (fibo (n + n))))
 *   in foo 2.
 * = (25, 25)
 * : nat * nat
 *
 * This is correct because we are looking for the fifth fibonacci number
 * but squared. That is 5 squared and that's equal to 25.
 *)

Proposition Cassini_s_identity_for_odd_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      S (square (fib ((S n) + (S n)))) =
      (fib (S ((S n) + (S n)))) * (fib (S (n + n))).
Proof.
  intro fib.
  intro H_spec_fib.
  intro n.

  unfold specification_of_fibonacci in H_spec_fib.
  destruct H_spec_fib as [H_fib_bc0 [H_fib_bc1 [H_fib_bc2 H_fib_ic]]].

  induction n as [ | n' IHn'].
  
  rewrite <- BinInt.ZL0.
  rewrite -> H_fib_bc2.
  rewrite -> unfold_square.
  rewrite -> mult_1_r.
  rewrite -> H_fib_ic.
  rewrite -> plus_0_r.
  rewrite -> H_fib_bc1.
  rewrite -> H_fib_bc2.
  rewrite -> mult_1_r.
  rewrite <- BinInt.ZL0.
  reflexivity.

  symmetry.
  rewrite -> plus_Sn_m at 1.
  rewrite -> H_fib_ic.
  rewrite -> mult_plus_distr_r.
  rewrite -> (plus_Sn_m n' (S n')) at 2.
  rewrite -> H_fib_ic.
  rewrite -> mult_plus_distr_l.
  rewrite <- plus_n_Sm at 3.
  rewrite <- (plus_n_Sm n' n') at 2.
  rewrite <- IHn'.
  rewrite -> plus_assoc.
  rewrite <- plus_n_Sm.
  rewrite -> unfold_square.
  rewrite <- (plus_Sn_m n' (S n')).
  rewrite <- plus_n_Sm at 2.
  rewrite <- plus_assoc.
  rewrite <- mult_plus_distr_r.
  rewrite <- H_fib_ic.
  rewrite <- plus_n_Sm.
  rewrite <- mult_plus_distr_l.
  rewrite <- H_fib_ic.
  rewrite <- unfold_square.
  rewrite -> plus_n_Sm.
  rewrite <- plus_Sn_m.
  reflexivity.
Qed.

(*
 * Compute
 *   let foo n :=
 *       (S (square (fibo ((S n) + (S n)))),
 *        (fibo (S ((S n) + (S n)))) * (fibo (S (n + n))))
 *   in foo 2.
 * = (65, 65)
 * : nat * nat
 *
 * This is correct because we are looking for the sixth fibonacci number
 * squared and plus one. The sixth fibonacci number is 8 and squared it is
 * equal to 64 and plus 1 it is 65.
 *)

(*
 * "My experience has been in a short 77 years that in the end when 
 * you fight for a desperate cause and have good reasons to fight, 
 * you usually win." By Edward Teller.
 *)
