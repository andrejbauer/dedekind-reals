(** Various lemmas that seem to be missing from the standard library. *)

Require Import QArith Qminmax Qabs.

Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).
Hint Unfold compose.
Notation "g 'o' f" := (compose g f) (at level 40, left associativity).

Definition const A B (y : B) : A -> B := (fun x => y).

(* power1 n A is the (n+1)-fold power of A, for instance power1 3 A is A * A * A * A. *)
Fixpoint power1 (n : nat) (A : Type) : Type :=
  match n with
    | 0%nat => A
    | S m => (power1 m A * A)%type
  end.

Notation "A ^^ n" := (power1 n A) (at level 8, left associativity) : type_scope.

Local Open Scope Q_scope.

Lemma Qeq_le (p q : Q) : p == q -> p <= q.
Proof.
  intro E.
  rewrite E.
  apply Qle_refl.
Defined.


Lemma Qopp_lt_compat : forall (p q : Q), p < q <-> -q < -p.
Proof.
  intros [a b] [c d].
  unfold Qlt. simpl.
  rewrite !Z.mul_opp_l. omega.
Defined.

Lemma Qplus_lt_lt_compat : forall (p q r s : Q), p < q -> r < s -> p + r < q + s.
Proof.
  auto using Qlt_le_weak, Qplus_lt_le_compat.
Qed.

Lemma Qmult_lt_positive : forall (p q : Q), 0 < p -> 0 < q -> 0 < p * q.
Proof.
  intros p q pPos qPos.
  rewrite <- (Qmult_0_l q).
  apply Qmult_lt_compat_r; assumption.
Qed.

Lemma Qmult_opp_r : forall (a b : Q), - (a * b) == a * -b.
Proof.
  intros (a1, a2) (b1, b2).
  unfold Qeq.
  simpl.
  ring.
Qed.

Lemma Qmult_opp_l : forall (a b : Q), - (a * b) == -a * b.
Proof.
  intros (a1, a2) (b1, b2).
  unfold Qeq.
  simpl.
  ring.
Qed.

Lemma Qlt_mult_neg_r (q r s : Q) : s < 0 -> (q < r <-> r * s < q * s).
Proof.
  intro A.
  split.
  - intro B.
    assert(C:=proj1 (Qlt_minus_iff s 0) A).
    rewrite (Qplus_0_l (-s)) in C.
    assert(E:=Qmult_lt_compat_r q r (-s) C B).
    apply Qopp_lt_compat.
    rewrite (Qmult_opp_r q s).
    rewrite (Qmult_opp_r r s).
    assumption.
  - intro B.
    assert(G:=Qmult_opp_r r s).
    assert(F:=Qmult_opp_r q s).
    assert(C:=proj1 (Qlt_minus_iff s 0) A).
    rewrite (Qplus_0_l (-s)) in C.
    assert(H:=Qeq_sym (- (r * s)) (r * - s) G).
    assert(D:=Qeq_sym (- (q * s)) (q * - s) F).
    assert(E:=Qmult_lt_r q r (-s) C).
    rewrite H in E.
    rewrite D in E.
    apply E.
    apply Qopp_lt_compat.
    rewrite (Qopp_involutive (r * s)).
    rewrite (Qopp_involutive (q * s)).
    assumption.
Qed.

Lemma Qlt_mult_neg_l (q r s : Q) : q < 0 -> (r < s <-> q * s < q * r).
Proof.
  intro A.
  split.
  - intro B.
    assert(C:=proj1 (Qlt_minus_iff q 0) A).
    assert(D:=Qplus_0_r (-q)).
    rewrite (Qplus_comm (-q) 0) in D.
    rewrite D in C.
    assert(E:=Qmult_lt_compat_r r s (-q) C B).
    apply Qopp_lt_compat.
    rewrite (Qmult_comm q r).
    rewrite (Qmult_comm q s).
    rewrite (Qmult_opp_r r q).
    rewrite (Qmult_opp_r s q).
    assumption.
  - intro B.
    assert(G:=Qmult_opp_l q s).
    assert(F:=Qmult_opp_l q r).
    assert(C:=proj1 (Qlt_minus_iff q 0) A).
    rewrite (Qplus_0_l (-q)) in C.
    assert(H:=Qeq_sym (- (q * s)) (- q * s) G).
    assert(D:=Qeq_sym (- (q * r)) ( -q * r) F).
    assert(E:=Qmult_lt_l r s (-q) C).
    rewrite H in E.
    rewrite D in E.
    apply E.
    apply Qopp_lt_compat.
    rewrite (Qopp_involutive (q * s)).
    rewrite (Qopp_involutive (q * r)).
    assumption.
Qed.

Lemma Qopp_lt_shift_l : forall (p q : Q), -p < q <-> -q < p.
Proof.
  intros p q; split; intro H.
  - rewrite <- (Qopp_involutive p).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
  - rewrite <- (Qopp_involutive q).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
Qed.

Lemma Qopp_lt_shift_r : forall (p q : Q), p < -q <-> q < -p.
Proof.
  intros p q; split; intro H.
  - rewrite <- (Qopp_involutive p).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
  - rewrite <- (Qopp_involutive q).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
Qed.

Lemma Qlt_minus_1 : forall q : Q, q + (-1#1) < q.
Proof.
  intro q.
  rewrite <- (Qplus_0_r q) at 2.
  apply Qplus_lt_r.
  compute; reflexivity.
Qed.

Lemma Qlt_plus_1 : forall q : Q, q < q + (1#1).
Proof.
  intro q.
  rewrite <- (Qplus_0_r q) at 1.
  apply Qplus_lt_r.
  compute; reflexivity.
Qed.

Lemma Qplus_nonneg_cone : forall q r, 0 <= q -> 0 <= r -> 0 <= q + r.
Proof.
  intros q r G H.
  setoid_replace 0 with (0 + 0) ; [idtac | (compute; reflexivity)].
  apply Qplus_le_compat; assumption.
Qed.

Lemma Qplus_zero_nonneg : forall q r, 0 <= q -> 0 <= r -> q + r == 0 -> q == 0 /\ r == 0.
Proof.
  intros q r Pq Pr H.
  split.
  - apply Qle_antisym ; auto.
    setoid_rewrite <- H.
    setoid_replace q with (q + 0) at 1 ; [idtac | ring].
    apply Qplus_le_r; assumption.
  - apply Qle_antisym ; auto.
    setoid_rewrite <- H.
    setoid_replace r with (0 + r) at 1 ; [idtac | ring].
    apply Qplus_le_l; assumption.
Qed.

Require Import Qpower.

Lemma Qpower_zero: forall p, ~p == 0 -> p^0 == 1.
Proof.
intros p H.
compute ; auto.
Qed.

Lemma Qopp_nonzero : forall p, ~ p == 0 -> ~ (-p) == 0.
Proof.
  intros p A.
  destruct (Q_dec 0 p) as [ [ B | C ] | D ].
  - apply Qlt_not_eq, (Qopp_lt_compat 0 p) ; assumption.
  - apply Qnot_eq_sym, Qlt_not_eq, (Qopp_lt_compat p 0) ; assumption.
  - elim A ; symmetry ; assumption.
Qed.

Lemma lt_from_le_nonzero: forall p, 0 <= p -> ~ p == 0 -> 0 < p.
Proof.
  intros p H G.
  destruct (Qlt_le_dec 0 p) as [K|L].
  - assumption.
  - absurd (p == 0) ; auto.
    apply Qle_antisym ; assumption.
Qed.

Lemma Qinv_gt_0_compat: forall a : Q, a < 0 -> / a < 0.
Proof.
  intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qinv_nonzero : forall p, ~ p == 0 -> ~ (/ p == 0).
Proof.
intros p H.
destruct (Q_dec 0 p) as [[A1|A2]|B].
- assert (F:= Qinv_lt_0_compat p A1).
  apply Qnot_eq_sym, (Qlt_not_eq 0 (/p) F).
- assert (F:= Qinv_gt_0_compat p A2).
  apply (Qlt_not_eq (/p) 0 F).
- assert (U := Qnot_eq_sym p 0 H).
  elim (U B).
Qed.

Lemma Qpower_nonzero : forall p n, ~ p==0 -> ~ p^n==0.
Proof.
intros p n G.
induction n.
- rewrite (Qpower_zero p).
  apply Q_apart_0_1.
  assumption.
- apply (Qpower_not_0_positive p p0 G).
- apply Qinv_nonzero, (Qpower_not_0_positive p p0 G).
Qed.

Lemma Qpower_strictly_pos : forall p n, 0 < p -> 0 < p^n.
Proof.
  intros p n G.
  apply lt_from_le_nonzero.
  - apply Qpower_pos, Qlt_le_weak; assumption.
  - apply Qpower_nonzero, Qnot_eq_sym, Qlt_not_eq ; assumption.
Qed.

Lemma pow_Q1_Qle : forall (q:Q) (n:nat),
    Qle 1 q
    -> Qle 1 (q^Z.of_nat n).
Proof.
  induction n.
  - intros. apply Qle_refl.
  - intros. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Qpower_plus.
    apply (Qle_trans _ (q ^ Z.of_nat n * 1)).
    rewrite Qmult_1_r. exact (IHn H). rewrite Qmult_le_l. exact H.
    apply Qpower_strictly_pos. apply (Qlt_le_trans 0 1 q).
    reflexivity. exact H. intro abs. rewrite abs in H.
    apply (Qle_not_lt _ _ H). reflexivity.
Qed.

Lemma pow_Q1_incr : forall (q:Q) (n p:nat),
    Qle 1 q
    -> le n p
    -> Qle (q ^ Z.of_nat n) (q^Z.of_nat p).
Proof.
  intros. destruct (Nat.le_exists_sub n p H0), H1. subst p.
  rewrite <- Qmult_1_l.
  rewrite Nat2Z.inj_add. rewrite Qpower_plus.
  rewrite Qmult_le_r. apply pow_Q1_Qle. exact H.
  apply Qpower_strictly_pos. apply (Qlt_le_trans 0 1 q).
  reflexivity. exact H. intro abs. rewrite abs in H.
  apply (Qle_not_lt _ _ H). reflexivity.
Qed.

Lemma Qabs_eq_0 : forall q, Qabs q == 0 -> q == 0.
Proof.
  intros q Hq.
  assert (Gq : Qabs q <= 0) ; [(rewrite Hq ; discriminate) | idtac].
  destruct (proj1 (Qabs_Qle_condition q 0) Gq).
  apply Qle_antisym; assumption.
Qed.

Lemma Qmult_le_compat_l : forall x y z, y <= z -> 0 <= x -> x*y <= x*z.
Proof.
  intros x y z A B.
  rewrite (Qmult_comm x y).
  rewrite (Qmult_comm x z).
  assert(C:=Qmult_le_compat_r y z x A B).
  assumption.
Qed.

Lemma Qmult_le_compat : forall q r s t,
  q <= r -> 0 <= s -> 0 <= q -> s <= t -> q * s <= r * t.
Proof.
  intros q r s t H1 H2 H3 H4.
  apply (Qle_trans _ (r * s)).
  - apply Qmult_le_compat_r ; assumption.
  - apply Qmult_le_compat_l.
    + assumption.
    + apply (Qle_trans _ q) ; assumption.
Qed.

Lemma middle_between : forall q r : Q,
    Qlt q r -> (Qlt q ((q+r)*(1#2)) /\ Qlt ((q+r)*(1#2)) r).
Proof.
  split.
  - rewrite <- (Qmult_lt_r _ _ (2#1)). apply (Qplus_lt_r _ _ (-q)).
    ring_simplify. apply H. reflexivity.
  - rewrite <- (Qmult_lt_r _ _ (2#1)). apply (Qplus_lt_r _ _ (-r)).
    ring_simplify. apply H. reflexivity.
Qed.

