(** When doing classical analysis, discontinuous real functions are often
    defined by testing a comparison, like
    f x := if 0 < x then 1 else 0.
    
    This requires the following disjunction in sort Type,
    { x < y } + { ~(x < y) }.

    We prove here that it implies the limited principle of omniscience,
    so it is not constructive. The proof assigns a rational sequence
    to each boolean sequence un, as
    vn n := if un n then 2^{-n} else 0.
    The series vn is convergent, because bounded by the convergent
    series 2^{-n}. *)

Require Import Logic.ConstructiveEpsilon.
Require Import QArith.
Require Import Qabs.
Require Import Qpower.
Require Import Cut.
Require Import Cauchy.
Require Import Additive.
Require Import MiscLemmas.
Require Import Qminmax.

Local Open Scope R_scope.

(* The limited principle of omniscience *)
Definition LPO : Set
  := forall (un : nat -> bool),
    { exists n : nat, un n = true } + { forall n:nat, un n = false }.

(* The LPO actually gives n in sort Type *)
Lemma LPO_epsilon : LPO -> forall (un : nat -> bool),
    { n : nat | un n = true } + { forall n:nat, un n = false }.
Proof.
  intros. destruct (H un).
  - apply constructive_indefinite_ground_description_nat in e.
    destruct e. left. exists x. exact e.
    intros. destruct (un n). left. reflexivity.
    right. discriminate.
  - right. exact e.
Qed.

(* The LPO lifts to decidable propositions *)
Lemma LPO_dec : forall (P : nat -> Prop),
    (forall n:nat, { P n } + { ~P n })
    -> LPO
    -> { n : nat | P n } + { forall n:nat, ~P n }.
Proof.
  intros. destruct (LPO_epsilon H0 (fun n => if H n then true else false)).
  - destruct s. left. exists x. destruct (H x). exact p. discriminate.
  - right. intros n abs. specialize (e n). destruct (H n).
    discriminate. contradiction.
Qed.

Lemma DecOrderImpliesLPO : (forall x:R, { 0 < x } + { ~(0 < x) }) -> LPO.
Proof.
  intros decOrder un. 
  pose (fun n:nat => if un n then (/2)^(Z.of_nat n) else 0%Q) as vn.
  assert (CauchyQ (sum_f_Q0 vn)).
  { apply (Cauchy_series_maj _ (fun n:nat => (/2)^(Z.of_nat n))).
    intro n. unfold vn. destruct (un n). rewrite Qabs_pos.
    apply Qle_refl. apply Qpower_pos. discriminate.
    rewrite Qabs_pos. apply Qpower_pos. discriminate. apply Qle_refl.
    apply (Un_cv_cauchy _ 2). exact GeoHalfSeries. }
  destruct (decOrder (CauchyQ_R (sum_f_Q0 vn) H)) as [H0|H0].
  - left. destruct H0 as [q [qPos H0]].
    destruct H0 as [r [n [rPos H0]]].
    specialize (H0 n (le_refl _)). simpl in qPos.
    apply (Qlt_trans 0 (q+r)) in H0. apply Find_positive_in_sum in H0.
    destruct H0. exists x. unfold vn in H0.
    destruct (un x) eqn:des. reflexivity.
    exfalso. exact (Qlt_irrefl 0 H0).
    intros. unfold vn. destruct (un k). apply Qpower_pos. discriminate.
    discriminate. rewrite <- Qplus_0_r. apply Qplus_lt_le_compat.
    exact qPos. apply Qlt_le_weak. exact rPos. 
  - right. intro n. apply Rnot_lt_le in H0.
    unfold Rle, CauchyQ_R in H0; simpl in H0.
    destruct (un n) eqn:des. 2: reflexivity. exfalso.
    (* Above n, the sequence sum_f_Q0 v stays above 2^(-n) *)
    specialize (H0 ((/2)^(2 + Z.of_nat n))).
    apply (Qlt_not_le ((/2)^(2 + Z.of_nat n)) 0).
    2: apply Qpower_pos; discriminate.
    apply H0. exists ((/2)^(2+ Z.of_nat n)), n.
    split. apply Qpower_strictly_pos. reflexivity.
    intros.
    setoid_replace ((/ 2) ^ (2 + Z.of_nat n) + (/ 2) ^ (2 + Z.of_nat n))%Q
      with ((/ 2) ^ (1 + Z.of_nat n)).
    apply (Qlt_le_trans _ ((/2) ^ Z.of_nat n)).
    do 2 rewrite Qinv_power.
    setoid_replace (/ 2 ^ (1 + Z.of_nat n)) with (/2 * / 2 ^ Z.of_nat n).
    rewrite <- (Qmult_lt_l _ _ (2 ^ Z.of_nat n)).
    rewrite Qmult_inv_r. field_simplify. reflexivity.
    apply Qpower_nonzero. intro abs. discriminate.
    apply Qpower_nonzero. intro abs. discriminate.
    apply Qpower_strictly_pos. reflexivity. 
    rewrite Qpower_plus. simpl. rewrite Qinv_mult_distr. reflexivity.
    intro abs. discriminate.
    apply (Qle_trans _ (vn n)).
    unfold vn. destruct (un n). apply Qle_refl. discriminate.
    apply (Qle_trans _ (sum_f_Q0 vn n)).
    apply pos_sum_le_last. intro k. unfold vn. destruct (un k).
    apply Qpower_pos. discriminate. apply Qle_refl. apply pos_sum_more.
    intro k. unfold vn. destruct (un k).
    apply Qpower_pos. discriminate. apply Qle_refl. exact H1.
    rewrite Qpower_plus. rewrite Qpower_plus. simpl. field.
    intro abs. discriminate. intro abs. discriminate.
Qed.


(* Conversely, we show that the lift of negative disjunctions
   enlarges both Dedekind and Cauchy reals to the same type of reals.
   This logical axiom is much weaker than sig_not_dec_T,
   one of the axioms of the stdlib classical reals. *)

Definition sig_not_dec_T : Type
  := forall P : Prop, { ~~P } + { ~P }.

Definition sig_or_not_dec_T : Type
  := forall P Q : Prop, (~P \/ ~Q) -> { ~P } + { ~Q }.

Lemma sig_not_implies_sig_or_not : sig_not_dec_T -> sig_or_not_dec_T.
Proof.
  intros X P Q. destruct (X P).
  - right. destruct H. contradiction. exact H.
  - left. exact n.
Qed.

Lemma sig_located : sig_or_not_dec_T -> forall (x:R) (q r : Q),
      Qlt q r -> { lower x q } + { upper x r }.
Proof.
  intros. assert ({ ~upper x (q+(r-q)/3) } + { ~lower x (r-(r-q)/3) }).
  { apply X. destruct (located x (q+(r-q)/3) (r-(r-q)/3)).
    - apply (Qmult_lt_l _ _ 3). reflexivity. field_simplify.
      apply (Qplus_lt_l _ _ (-r-q)). ring_simplify. exact H.
    - left. intro abs. apply (disjoint x _ (conj H0 abs)).
    - right. intro abs. apply (disjoint x _ (conj abs H0)). }
  destruct H0.
  - left. destruct (located x q (q+(r-q)/3)).
    apply (Qmult_lt_l _ _ 3). reflexivity. field_simplify. 
    apply (Qplus_lt_l _ _ (-2*q)). ring_simplify. exact H.
    exact H0. contradiction.
  - right. destruct (located x (r-(r-q)/3) r).
    apply (Qmult_lt_l _ _ 3). reflexivity. field_simplify. 
    apply (Qplus_lt_l _ _ (-2*r)). ring_simplify. exact H.
    contradiction. exact H0.
Qed.

(* This obscure negociation with Coq's structural recursion
   can probably be rephrased as a 
   constructive_indefinite_ground_description_nat. *)
Inductive BoundSearchTerminates (x : R) : Prop := 
(* When x is negative, its bound is 0 *)
| xIsNegative : upper x 0 -> BoundSearchTerminates x
(* When x-1 has a bound, that bound plus 1 is a bound of x *)
| xStepSearch : BoundSearchTerminates (x - 1) -> BoundSearchTerminates x.

Fixpoint fix_bound_epsilon (x : R) (term : BoundSearchTerminates x) { struct term }
  : sig_or_not_dec_T -> { q : Q | upper x q }.
Proof.
  intro X. destruct (sig_located X x 0 1 (eq_refl _)).
  - destruct (fix_bound_epsilon
                (x-1) (match term with
                       | xIsNegative _ u => False_ind _ (disjoint x 0 (conj l u))
                       | xStepSearch _ s => s end) X).
    exists (x0+1)%Q. destruct u as [r [s u]]. apply (upper_upper x r).
    2: apply u. simpl in u. apply (Qplus_lt_l _ _ s), (Qlt_trans _ x0).
    apply u. apply (Qplus_lt_l _ _ (-x0-s)). ring_simplify.
    destruct u,H0. ring_simplify in H1. exact H1.
  - exists 1%Q. exact u.
Qed.

Lemma upper_bound_epsilon :
  sig_or_not_dec_T -> forall x:R, { q : Q | upper x q }.
Proof.
  intros.
  destruct (fix_bound_epsilon x).
  - (* Now in sort Prop, can destruct : *)
    destruct (upper_bound x) as [[a b] qmaj].
    assert (forall (n:nat) (y:R), upper y (Z.of_nat n # 1) -> BoundSearchTerminates y).
    { induction n. intros. apply xIsNegative.
      apply (upper_proper y 0%Q (Z.of_nat 0#1)). reflexivity. exact H.
      intros. apply xStepSearch, IHn.
      apply R_lt_Q_iff.
      apply (upper_proper y (Z.of_nat (S n) # 1) (1+ (Z.of_nat n#1))%Q) in H.
      apply R_lt_Q_iff in H.
      apply (Rplus_lt_reg_r 1). unfold Rminus.
      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
      rewrite R_of_Q_plus in H. exact H.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      unfold Qeq. do 2 rewrite Z.mul_1_r. 
      unfold Qplus. unfold Qnum,Qden. ring. } 
    destruct a.
    + apply xIsNegative. apply (upper_proper x 0%Q (0#b)).
      reflexivity. exact qmaj.
    + specialize (H (Pos.to_nat p) x). apply H.
      rewrite positive_nat_Z. apply (upper_le x (Z.pos p # b)).
      exact qmaj. unfold Qle; simpl.
      do 2 rewrite Pos2Z.inj_mul. apply Z.mul_le_mono_nonneg_l.
      apply Pos2Z.is_nonneg. unfold Z.le. rewrite <- Pos2Z.inj_compare.
      apply Pos2Nat.inj_le. destruct (Pos.to_nat b) eqn:des.
      exfalso. pose proof (Pos2Nat.is_pos b). rewrite des in H0.
      inversion H0. apply le_n_S. apply le_0_n.
    + apply xIsNegative. apply (upper_upper x (Z.neg p # b)).
      reflexivity. exact qmaj.
  - exact X. 
  - exists x0. exact u.
Qed.

Lemma lower_bound_epsilon :
  sig_or_not_dec_T -> forall x:R, { q : Q | lower x q }.
Proof.
  intros. destruct (upper_bound_epsilon X (-x)).
  exists (-x0)%Q. exact u.
Qed.

