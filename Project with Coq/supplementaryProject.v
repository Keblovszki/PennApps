(* Name: Hannibal Krabbe-keblovszki
 * Student number: 20102295
 * Project for introduction to functional programming
 *
 * Supplementary project: Exponentiating a 2x2 matrix 
 * Filename: supplementrayProject.v
 *)

Require Import Arith.

(* ----------------------------------*)

Inductive matrix_2_2 : Type :=
  | cm : nat -> nat -> nat -> nat -> matrix_2_2.

(* Defined a matrix: (a, b, c, d)
 * (a, b)
 * (c, d) 
 * cm is an abbreviation for construct matrix.
 *)

Definition matrix_1_2_3_4 :=
  cm 1 2 3 4.

Definition matrix_4_3_2_1 :=
  cm 4 3 2 1.

Definition matrix_1_1_1_0 :=
  cm 1 1 1 0.

Definition matrix_0_1_1_1 :=
  cm 0 1 1 1.

Definition matrix_2_1_1_1 :=
  cm 2 1 1 1.

(* 
 * "If you spend too much time warming up, you'll miss the race. If you
 *  don't warm up at all, you may not finish the race." by Grand Heidrich 
 *)

(* Specification for adding matrices *)
Definition specification_of_plus_matrices (plus : matrix_2_2 ->
                                                  matrix_2_2 ->
                                                  matrix_2_2) :=
  forall plus : (matrix_2_2 -> matrix_2_2 -> matrix_2_2),
    forall a b c d e f g h : nat,
      plus (cm a b c d) (cm e f g h) = cm (a + e) (b + f) (c + g) (d + h).

Theorem there_is_only_one_plus_matrices :
  forall plus1 plus2 : (matrix_2_2 -> matrix_2_2 -> matrix_2_2),
    specification_of_plus_matrices plus1 ->
    specification_of_plus_matrices plus2 ->
    forall m1 m2 : matrix_2_2,
      plus1 m1 m2 = plus2 m1 m2. 
Proof.
  intros plus1 plus2.
  intros H_spec_plus1 H_spec_plus2.
  intros m1 m2.

  (* you can do it without these two guys
  unfold specification_of_plus_matrices in H_spec_plus1.
  unfold specification_of_plus_matrices in H_spec_plus2.
   *) 

  case m1 as [a b c d].
  case m2 as [e f g h].
  
  rewrite -> H_spec_plus1.
  rewrite -> H_spec_plus2.
  reflexivity.
Qed.

Definition add_matrix (m1 m2 : matrix_2_2) : matrix_2_2 :=
  match m1 with
    | cm a b c d => match m2 with
                      | cm e f g h =>
                        cm (a + e) (b + f) (c + g) (d + h)
                    end
  end.

Lemma unfold_add_matrix :
  forall a b c d e f g h : nat,
    add_matrix (cm a b c d) (cm e f g h) = cm (a + e) (b + f) (c + g) (d + h).
Proof.
  intros a b c d e f g h.
  unfold add_matrix.
  reflexivity.
Qed.

(*
 * Compute add_matrix matrix_1_2_3_4 matrix_4_3_2_1.
 * = cm 5 5 5 5
 * : matrix_2_2
 * 
 * Compute add_matrix matrix_1_2_3_4 matrix_1_1_1_0.
 * = cm 2 3 4 4
 * : matrix_2_2
 *)

(* Specification for multiplying matrices *)

(*
 * "Writing is an exploration. You start from nothing and learn as you go."
 * By E. L. Doctorow
 *)

Definition specification_of_mul_matrices (mul : matrix_2_2 ->
                                                  matrix_2_2 ->
                                                  matrix_2_2) :=
  forall mul : (matrix_2_2 -> matrix_2_2 -> matrix_2_2),
    forall a b c d e f g h : nat,
      mul (cm a b c d) (cm e f g h) = cm ((a*e)+(b*g)) ((a*f)+(b*h))
                                         ((c*e)+(d*g)) ((c*f)+(d*h)).

Theorem there_is_only_one_mul_matrices :
  forall mul1 mul2 : (matrix_2_2 -> matrix_2_2 -> matrix_2_2),
    specification_of_mul_matrices mul1 ->
    specification_of_mul_matrices mul2 ->
    forall m1 m2 : matrix_2_2,
      mul1 m1 m2 = mul2 m1 m2. 
Proof.
  intros mul1 mul2.
  intros H_spec_mul1 H_spec_mul2.
  intros m1 m2.

  (* Again without these two guys:
  unfold specification_of_mul_matrices in H_spec_mul1.
  unfold specification_of_mul_matrices in H_spec_mul2.
   *)

  case m1 as [a b c d].
  case m2 as [e f g h].
  
  rewrite -> H_spec_mul1.
  rewrite -> H_spec_mul2.
  reflexivity.
Qed.

Definition mul_matrix (m1 m2 : matrix_2_2) : matrix_2_2 :=
  match m1 with
    | cm a b c d => match m2 with
                      | cm e f g h =>
                        cm ((a*e)+(b*g)) ((a*f)+(b*h))
                           ((c*e)+(d*g)) ((c*f)+(d*h))
                    end
  end.

(*
 * Compute mul_matrix matrix_1_2_3_4 matrix_4_3_2_1.
 * = cm 8 5 20 13
 * : matrix_2_2
 *
 * Compute mul_matrix matrix_1_1_1_0 matrix_1_1_1_0.
 * = cm 2 1 1 1
 * : matrix_2_2
 * 
 * Compute mul_matrix matrix_2_1_1_1 matrix_1_1_1_0.
 * = cm 3 2 2 1
 * : matrix_2_2
 * 
 * Hmm.. Seems like the product of those matrices must have some 
 * connection to the fibonacci-numbers but which one? Lets find out later.
 *)

Lemma unfold_mul_matrix :
  forall a b c d e f g h : nat,
    mul_matrix (cm a b c d) (cm e f g h) = cm ((a*e)+(b*g)) ((a*f)+(b*h))
                                              ((c*e)+(d*g)) ((c*f)+(d*h)).
Proof.
  intros a b c d e f g h.
  unfold mul_matrix.
  reflexivity.
Qed.

(* two helping lemmas *)

Lemma plus_comm_over_paren_l : 
  forall a b c,
    a + (b + c) = b + (a + c).
Proof.                      
  intros a b c.
  rewrite ->2 plus_assoc.
  rewrite -> (plus_comm a b).
  reflexivity.
Qed.

Lemma plus_comm_over_paren_r : 
  forall a b c,
    (a + b) + c = (a + c) + b.
Proof.
  intros a b c.
  rewrite <- plus_assoc.
  rewrite (plus_comm b c).
  rewrite plus_assoc.
  reflexivity.
Qed.

Lemma matrix_mul_assoc : 
  forall m1 m2 m3 : matrix_2_2,
    mul_matrix m1 (mul_matrix  m2 m3) = mul_matrix (mul_matrix m1 m2) m3.
Proof.
  intros m1 m2 m3.

  case m1 as [a b c d].
  case m2 as [e f g h].
  case m3 as [i j k l].

  rewrite ->4 unfold_mul_matrix.
  rewrite ->8 mult_plus_distr_l.
  rewrite ->16 mult_assoc.
  rewrite ->4 plus_assoc.
  symmetry.
  rewrite ->8 mult_plus_distr_r.
  rewrite ->4 plus_assoc.
  rewrite -> (plus_comm_over_paren_r _ _ (a*f*k)).
  rewrite -> (plus_comm_over_paren_r _ _ (a*f*l)).
  rewrite -> (plus_comm_over_paren_r _ _ (c*f*k)).
  rewrite -> (plus_comm_over_paren_r _ _ (c*f*l)).
  reflexivity.
Qed.

Definition specification_of_exp_matrices (exp : matrix_2_2 ->
                                               nat -> matrix_2_2) :=
  (forall m : matrix_2_2,
     exp m 0 = cm 1 0 0 1)
  /\
  (forall m : matrix_2_2,
   forall n : nat,
     exp m (S n) = mul_matrix m (exp m n)).

Fixpoint exp_matrix (m : matrix_2_2) (n : nat) : matrix_2_2 :=
  match n with
    | 0 => cm 1 0 0 1
    | (S n') => mul_matrix m (exp_matrix m n')
  end.

(*
 * Compute exp_matrix (cm 1 1 1 1) 4. 
 * = cm 8 8 8 8
 * : matrix_2_2
 *
 * Compute exp_matrix (cm 1 2 2 1) 1
 * = cm 1 2 2 1
 * : matrix_2_2
 *
 *)

Lemma unfold_exp_matrices_bc :
  forall m : matrix_2_2,
    exp_matrix m 0 = cm 1 0 0 1.
Proof.
  intro m.
  unfold exp_matrix.
  reflexivity.
Qed.

Lemma unfold_exp_matrices_ic :
  forall m : matrix_2_2,
    forall n : nat,
      exp_matrix m (S n) = mul_matrix m (exp_matrix m n).
Proof.
  intros m n.
  unfold exp_matrix; fold exp_matrix.
  reflexivity.
Qed.

Theorem there_is_only_one_exp_matrices :
  forall exp1 exp2 : (matrix_2_2 -> nat -> matrix_2_2),
    specification_of_exp_matrices exp1 ->
    specification_of_exp_matrices exp2 ->
    forall (m : matrix_2_2) (n : nat),
      exp1 m n = exp2 m n. 
Proof.
  intros exp1 exp2.
  intros H_spec_exp1 H_spec_exp2.
  intros m n.

  unfold specification_of_exp_matrices in H_spec_exp1.
  destruct H_spec_exp1 as [H_exp1_bc H_exp1_ic].

  unfold specification_of_exp_matrices in H_spec_exp2.
  destruct H_spec_exp2 as [H_exp2_bc H_exp2_ic].

  induction n as [ | n' IHn'].
 
  rewrite -> H_exp1_bc.
  rewrite -> H_exp2_bc.
  reflexivity.

  rewrite -> H_exp1_ic.
  rewrite -> IHn'.
  rewrite -> H_exp2_ic.
  reflexivity.
Qed.

(* -- And now for the fibonacci numbers -- *)

(* 
 * "The human mind has first to construct forms, independently, 
 * before we can find them in things." By Albert Einstein.
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

Fixpoint fib (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib n' + fib n''
              end
  end.

Lemma unfold_fib_bc0 :
  fib 0 = 0.
Proof.
  unfold fib.
  reflexivity.
Qed.

Lemma unfold_fib_bc1 :
  fib 1 = 1.
Proof.
  unfold fib.
  reflexivity.
Qed.

Lemma unfold_fib_bc2 :
  fib 2 = 1.
Proof.
  unfold fib.
  reflexivity.
Qed.

Lemma unfold_fib_ic :
  forall n : nat,
    fib (S (S n)) = fib (S n) + fib n.
Proof.
  intro n.
  unfold fib; fold fib.
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

(*
 * Compute exp_matrix matrix_1_1_1_0 2.
 * = cm 2 1 1 1
 * : matrix_2_2
 *
 * Compute exp_matrix matrix_1_1_1_0 3.
 * = cm 3 2 2 1
 * : matrix_2_2
 *
 * Compute exp_matrix matrix_1_1_1_0 4.
 * = cm 5 3 3 2
 * : matrix_2_2
 *
 * Compute exp_matrix matrix_1_1_1_0 5.
 * = cm 8 5 5 3
 * : matrix_2_2
 *
 * So the pattern is:
 * forall n : nat
 * Compute exp_matrix matrix_1_1_1_0 (S n)
 * = cm (fib (S (S n))) (fib (S n)) (fib (S n)) (fib n)
 * : matrix_2_2. 
 *)

(*
 * "Beautiful things make people happy." By Eva Zeisel
 *)

Theorem exp_matrix_is_a_fib_matrix :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      exp_matrix (cm 1 1 1 0) (S n) =
      cm (fib (S (S n))) (fib (S n)) (fib (S n)) (fib n).
Proof.
  intro fib.
  intro H_spec_fib.
  intro n.

  unfold specification_of_fibonacci in H_spec_fib.
  destruct H_spec_fib as [H_fib_bc0 [H_fib_bc1 [H_fib_bc2 H_fib_ic]]].

  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_matrices_ic.
  rewrite -> unfold_exp_matrices_bc.
  rewrite -> unfold_mul_matrix.
  rewrite -> mult_1_l.
  rewrite -> mult_0_r.
  rewrite -> mult_0_r.
  rewrite -> mult_1_r.
  rewrite ->2 plus_0_r.
  rewrite -> plus_0_l.
  rewrite -> H_fib_bc0.
  rewrite -> H_fib_bc1.
  rewrite -> H_fib_bc2.
  reflexivity.

  rewrite -> unfold_exp_matrices_ic.
  rewrite -> IHn'.
  rewrite -> unfold_mul_matrix.
  rewrite ->3 mult_1_l.
  rewrite ->2 mult_0_l.
  rewrite ->2 plus_0_r.
  rewrite <-2 H_fib_ic.
  reflexivity.
Qed.

Lemma increment :
  forall n : nat,
    S n = n + 1.
Proof.
  intro n.
  rewrite <- plus_n_Sm.
  rewrite -> plus_0_r.
  reflexivity.
Qed.

(* -- Further properties about matrices -- *)

Theorem matrix_exp_n_with_1_1_0_1_is :
  forall n : nat,
    exp_matrix (cm 1 1 0 1) n = cm 1 n 0 1.
Proof.  
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_matrices_bc.
  reflexivity.

  rewrite -> unfold_exp_matrices_ic.
  rewrite -> IHn'.
  rewrite -> unfold_mul_matrix.
  rewrite -> mult_1_r.
  rewrite -> mult_0_r.
  rewrite ->2 mult_0_l.
  rewrite -> mult_1_l.
  rewrite ->2 plus_0_r.
  rewrite -> plus_0_l.
  rewrite <- increment.
  reflexivity.
Qed.

Theorem matrix_exp_n_with_1_0_1_1_is :
  forall n : nat,
    exp_matrix (cm 1 0 1 1) n = cm 1 0 n 1.
Proof.
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_matrices_bc.
  reflexivity.

  rewrite -> unfold_exp_matrices_ic.
  rewrite -> IHn'.
  rewrite -> unfold_mul_matrix.
  rewrite -> mult_1_r.
  rewrite -> mult_0_r.
  rewrite ->2 mult_0_l.
  rewrite -> mult_1_l.
  rewrite ->2 plus_0_r.
  rewrite -> plus_0_l.
  rewrite -> plus_comm.
  rewrite <- increment.
  reflexivity.
Qed.

(*
 * To transpose a matrix means that
 * (a, b)
 * (c, d)
 * transposed is
 * (a, c)
 * (b, d)
 *)

(*
 * "Success is not final, failure is not fatal: it is the courage to
 * continue that counts." By Winston Churchill
 *)

Definition specification_of_transpose_matrices (trans : matrix_2_2 ->
                                                        matrix_2_2) :=
  forall trans : (matrix_2_2 -> matrix_2_2),
    forall a b c d : nat,
      trans (cm a b c d) = cm a c b d.

Theorem there_is_only_one_transpose_matrices :
  forall trans1 trans2 : (matrix_2_2 -> matrix_2_2),
    specification_of_transpose_matrices trans1 ->
    specification_of_transpose_matrices trans2 ->
    forall m : matrix_2_2,
      trans1 m = trans2 m.
Proof.
  intros trans1 trans2.
  intros H_spec_trans1 H_spec_trans2.
  intros m.

  (* Well again we don't need these two guys:
  unfold specification_of_transpose_matrices in H_spec_trans1.
  unfold specification_of_transpose_matrices in H_spec_trans2.
   *) 

  case m as [a b c d].
  
  rewrite -> H_spec_trans1.
  rewrite -> H_spec_trans2.
  reflexivity.
Qed.

Fixpoint trans_matrix (m : matrix_2_2) : matrix_2_2 :=
  match m with
    | cm a b c d => cm a c b d
  end.

(*
 * Compute trans_matrix (cm 1 3 2 4).
 * = cm 1 2 3 4
 * : matrix_2_2
 *  
 * Compute trans_matrix (cm 11 3 2 44).
 * = cm 11 2 3 44
 * : matrix_2_2  
 *
 * "It works - wuhu.", By Hannibal Krabbe-Keblovszki
 *)

Lemma unfold_trans_matrix :
  forall a b c d : nat,
    trans_matrix (cm a b c d) = cm a c b d.
Proof.
  intros a b c d.
  unfold trans_matrix.
  reflexivity. 
Qed.

(*
 * Make everything as simple as possible, but not simpler.
 * By Albert Einstein
 *)

Theorem matrix_transposition_is_involutive :
  forall m : matrix_2_2,
    trans_matrix (trans_matrix m) = m.
Proof.
  intro m.

  case m as [a b c d].

  rewrite -> unfold_trans_matrix.
  rewrite -> unfold_trans_matrix.
  reflexivity.
Qed.

Lemma matrix_comm_with_exponent :
  forall m : matrix_2_2,
    forall n : nat,
      mul_matrix m (exp_matrix m n) = mul_matrix (exp_matrix m n) m.
Proof.
  intros m n.
  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_matrices_bc.
  
  case m as [a b c d].
  rewrite ->2 unfold_mul_matrix.
  rewrite ->4 mult_0_r.
  rewrite ->4 mult_1_r.
  rewrite ->2 plus_0_r.
  rewrite ->2 plus_0_l.
  symmetry.
  rewrite ->4 mult_1_l.
  rewrite ->4 mult_0_l.
  rewrite ->2 plus_0_r.
  rewrite ->2 plus_0_l.
  reflexivity.

  rewrite -> unfold_exp_matrices_ic.
  rewrite -> IHn'.
  rewrite -> matrix_mul_assoc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Lemma about_transposition_matrices :
  forall m1 m2 : matrix_2_2,
    trans_matrix (mul_matrix m1 m2)
    = mul_matrix (trans_matrix m2) (trans_matrix m1).
Proof.
  intros m1 m2.
  
  case m1 as [a b c d].
  case m2 as [e f g h].

  rewrite -> unfold_mul_matrix.
  rewrite ->3 unfold_trans_matrix.
  rewrite -> unfold_mul_matrix.
  symmetry.
  rewrite -> (mult_comm e a).
  rewrite -> (mult_comm g b).
  rewrite -> (mult_comm e c).
  rewrite -> (mult_comm g d).
  rewrite -> (mult_comm f a).
  rewrite -> (mult_comm h b).
  rewrite -> (mult_comm f c).
  rewrite -> (mult_comm h d).
  reflexivity.
Qed.

Theorem matrix_transposition :
  forall m : matrix_2_2,
    forall n : nat,
      trans_matrix (exp_matrix m n)
      = exp_matrix (trans_matrix m) n.
Proof.
  intros m n.
  case m as [a b c d].

  induction n as [ | n' IHn'].

  rewrite -> unfold_exp_matrices_bc.
  rewrite -> unfold_trans_matrix.
  rewrite -> unfold_trans_matrix.
  rewrite -> unfold_exp_matrices_bc.
  reflexivity.

  rewrite ->2 unfold_exp_matrices_ic.
  rewrite -> about_transposition_matrices.
  rewrite -> IHn'.
  rewrite <- matrix_comm_with_exponent.
  reflexivity.
Qed.  

(* After introducing the tranpose of a matrix we need to revisit this 
 * theorem again *)

Theorem matrix_exp_n_with_1_0_1_1_is_revisited :
  forall n : nat,
    exp_matrix (cm 1 0 1 1) n = trans_matrix (exp_matrix (cm 1 1 0 1) n).
Proof.
  intro n.
  rewrite -> matrix_exp_n_with_1_0_1_1_is.
  rewrite -> matrix_exp_n_with_1_1_0_1_is.
  rewrite -> unfold_trans_matrix.
  reflexivity.
Qed.

Theorem matrix_exp_n_with_1_1_0_1_is_revisited :
  forall n : nat,
    exp_matrix (cm 1 1 0 1) n = trans_matrix (exp_matrix (cm 1 0 1 1) n).
Proof.
  intro n.
  rewrite -> matrix_exp_n_with_1_0_1_1_is.
  rewrite -> matrix_exp_n_with_1_1_0_1_is.
  rewrite -> unfold_trans_matrix.
  reflexivity.
Qed.

(*
 * "I've got a theory that if you give 100% all of the time, 
 * somehow things will work out in the end." By Larry Bird
 *)