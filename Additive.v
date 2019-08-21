(** The additive structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut.
Require Import Archimedean.

Local Open Scope Q_scope.

(** Addition. *)
Definition Rplus : R -> R -> R.
Proof.
  intros x y.
  refine {|
      lower := (fun q => exists r s, q < r + s /\ lower x r /\ lower y s) ;
      upper := (fun q => exists r s, r + s < q /\ upper x r /\ upper y s)
    |}.
  - intros u v Euv.
    split ; intros [r [s [H1 [H2 H3]]]] ; exists r, s ; split ; auto.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite Euv ; assumption.
  - intros u v Euv.
    split ; intros [r [s [H1 [H2 H3]]]] ; exists r, s ; split ; auto.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite Euv ; assumption.
  - destruct (lower_bound x) as [q H].
    destruct (lower_bound y) as [r G].
    exists (q + r).
    destruct (lower_open x q H) as [q' [Lqq' H']].
    destruct (lower_open y r G) as [r' [Lrr' G']].
    exists q', r' ; split ; auto.
    apply Qplus_lt_lt_compat ; assumption.
  - destruct (upper_bound x) as [q H].
    destruct (upper_bound y) as [r G].
    exists (q+r).
    destruct (upper_open x q H) as [q' [Lqq' H']].
    destruct (upper_open y r G) as [r' [Lrr' G']].
    exists q', r';split; auto.
    apply Qplus_lt_lt_compat ; assumption.
  - intros q r Lqr [r' [s' [H1 [H2 H3]]]].
    exists r', s' ; split ; auto.
    transitivity r ; assumption.
  - intros q [r [s [H1 [H2 H3]]]].
    exists ((q + r + s) * (1#2)) ; split.
    + apply (Qle_lt_trans q  ((q+q)*(1#2)) ((q + r + s) * (1 # 2))). 
      ring_simplify; apply Qle_refl.
      apply Qmult_lt_compat_r; [reflexivity | idtac].
       apply (Qplus_lt_r _ _ (-q)); ring_simplify; assumption.
    + exists r, s ; split ; auto.
      setoid_replace (r+s) with ((r+s+r+s)*(1#2)).
      apply Qmult_lt_compat_r. reflexivity.
      destruct (Qplus_lt_l q (r+s) (r+s)) .
      setoid_replace (q+r+s) with (q+(r+s)); [idtac | ring]. 
      setoid_replace (r+s+r+s) with (r+s+(r+s)); [auto | ring].
      ring_simplify; ring. 
  - intros q r Lqr [r' [s' [H1 [H2 H3]]]].
    exists r', s'; split; auto.
    transitivity q; assumption.
  - intros q [r [s [H1 [H2 H3]]]].
    exists ((q + r + s) * (1#2)) ; split.
    +apply (Qlt_le_trans ((q + r + s) * (1 # 2)) ((q+q)*(1#2)) q). 
     apply Qmult_lt_compat_r; [reflexivity | idtac].
     destruct (Qplus_lt_r (r+s) q q).
     setoid_replace (q+r+s) with (q+(r+s)); [apply H0;assumption|idtac].
     ring_simplify; apply Qeq_refl.
     ring_simplify; apply Qle_refl.
    + exists r, s ; split ; auto.
      setoid_replace (r+s) with ((r+s+r+s)*(1#2)); [idtac|ring].
      apply Qmult_lt_compat_r; [reflexivity | idtac].
      destruct (Qplus_lt_l (r+s) q (r+s)) .
      apply (Qplus_lt_r _ _ (-r-s)); ring_simplify; assumption.
  - intros q [[r [s [H1 [H2 H3]]]] [r' [s' [G1 [G2 G3]]]]].
    apply (Qlt_irrefl q).
    transitivity (r + s) ; auto.
    transitivity (r' + s') ; auto.
    apply Qplus_lt_lt_compat ; [apply (lower_below_upper x) | apply (lower_below_upper y) ] ; auto.
  - intros q r H.
    assert (G : ((r-q)*(1 # 2) > 0)%Q).
    apply (Qmult_lt_r _ _ (2#1)); [reflexivity|ring_simplify].
    apply (Qplus_lt_r _ _ q); ring_simplify; assumption.
    destruct (archimedean x _ G) as [xL [xU [xA [xB xC]]]].
    destruct (archimedean y _ G) as [yL [yU [yA [yB yC]]]].
    destruct (Qlt_le_dec (xL+yL) r) as [E1 | E2].
    + destruct (Qlt_le_dec (xU+yU) r) as [F1 | F2].
      * right.
        exists xU, yU; auto.
      * {
        left.
        exists xL, yL; split; auto.
        assert (r-xL-yL<r-q).
          -setoid_replace (r-q) with ((r-q)*(1#2) + (r-q)*(1#2));[idtac|ring].
           apply (Qlt_trans (r-xL-yL) ((r-q)*(1#2)+yU-yL) ((r-q)*(1#2)+(r-q)*(1#2))).    
           + apply (Qle_lt_trans (r-xL-yL) (xU-xL+yU-yL) ((r-q)*(1#2)+yU-yL)).
             * apply (Qplus_le_r _ _ (xL+yL)%Q) ; ring_simplify ; auto.
             * apply (Qplus_lt_r _ _ (-yU+yL)%Q) ; ring_simplify. 
               setoid_replace ((1 # 2) * r + (-1 # 2) * q) with ((r - q) * (1 # 2)).
               auto. ring_simplify; reflexivity.
           + setoid_replace ((r-q)*(1#2)+yU-yL) with ((r-q)*(1#2)+(yU-yL)).
             apply Qplus_lt_r; auto.
             ring_simplify; reflexivity.
          -apply (Qplus_lt_l _ _ (r-xL-yL-q)); ring_simplify.
           setoid_replace ((-1#1)*q+r) with (r-q);[auto|apply (Qplus_comm ((-1#1)*q)r)].
        }
    +left. 
     exists xL, yL; split; auto.
     apply (Qlt_le_trans q r (xL+yL)); auto. 
Defined.

(** Opposite value. *)
Definition Ropp : R -> R.
Proof.
  intro x.
  refine {| lower := (fun q => upper x (-q)); upper := (fun r => lower x (-r)) |}.
  - intros ? ? H. rewrite H; tauto.
  - intros ? ? H. rewrite H; tauto.
  - destruct (upper_bound x) as [r H].
    exists (- r).
    rewrite (Qopp_involutive r); assumption.
  - destruct (lower_bound x) as [q H].
    exists (- q).
    rewrite (Qopp_involutive q); assumption.
  - intros q r H G.
    apply (upper_upper _ (- r) _); [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (upper_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_r; assumption.
    rewrite Qopp_involutive; assumption.
  - intros q r H G.
    apply (lower_lower _ _ (- q)) ; [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (lower_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_l; assumption.
    rewrite Qopp_involutive; assumption.
  - intros.
    pose (H := disjoint x (- q)).
    tauto.
  - intros q r H.
    destruct (located x (-r) (-q)).
    + apply Qopp_lt_compat; rewrite 2 Qopp_involutive; assumption.
    + right; assumption.
    + left; assumption.
Defined.

Definition Rminus x y := Rplus x (Ropp y).

(** Notation for the ring structure. *)

Infix "+" := Rplus : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "-" := Rminus : R_scope.

(** The arithmetical operations are proper with respect to equality. *)

Instance Rplus_comp : Proper (Req ==> Req ==> Req) Rplus.
Proof.
  intros x y Exy u v Euv.
  split ; intros q [s [r ?]].
  - exists s, r. setoid_rewrite <- Exy ; setoid_rewrite <- Euv ; auto.
  - exists s, r. setoid_rewrite -> Exy ; setoid_rewrite -> Euv ; auto.
Qed.

Instance Ropp_comp : Proper (Req ==> Req) Ropp.
Proof.
  intros x y E.
  split ; intro q ; simpl ; rewrite E ; auto.
Qed.

Local Open Scope R_scope.

(** Properties of addition. *)

Lemma sum_interval_lower :
  forall (x y : R) (a b : Q),
    lower x a
    -> lower y b
    -> lower (x+y)%R (a + b).
Proof.
  intros.
  destruct (lower_open x a H), (lower_open y b H0).
  exists x0,x1. split.
  apply Qplus_lt_le_compat. apply H1. apply Qlt_le_weak. apply H2.
  split. apply H1. apply H2.
Qed.

Lemma sum_interval_upper :
  forall (x y : R) (a b : Q),
    upper x a
    -> upper y b
    -> upper (x+y)%R (a + b).
Proof.
  intros.
  destruct (upper_open x a H), (upper_open y b H0).
  exists x0,x1. split.
  apply Qplus_lt_le_compat. apply H1. apply Qlt_le_weak. apply H2.
  split. apply H1. apply H2.
Qed.

Lemma Rplus_assoc (x y z : R) : (x + y) + z == x + (y + z).
Proof.
  split.
  - intros q [s [r [G1 [[s' [r' [K1 [K2 K3]]]] G3]]]].
    exists s', (r + r')%Q ; split.
    + rewrite (Qplus_comm r r').
      rewrite (Qplus_assoc s' r' r).
      rewrite G1.
      apply Qplus_lt_l.
      assumption.
    + split ; auto.
      destruct (lower_open z r) as [t [H1 H2]]. assumption. 
      exists r', t; split; auto.
      rewrite (Qplus_comm r r').
      apply Qplus_lt_r; auto.
  - intros q [x' [yz' [H [Hx [y' [z' [H1 [Hy Hz]]]]]]]].
    exists (x' + y')%Q, z' ; split.
    + transitivity (x' + yz')%Q ; auto.
      apply (Qplus_lt_r _ _ (-x')); ring_simplify; assumption. 
    + split ; auto.
      destruct (lower_open x x') as [t [G1 G2]] ; auto.
      exists t, y'; split; auto.
      apply Qplus_lt_l; auto.
Qed.

Lemma Rplus_comm (x y : R) : x + y == y + x.
Proof.
  split ; intros q [r [s [G1 [G2 G3]]]] ; exists s, r ; split ; auto ;
  setoid_rewrite (Qplus_comm s r) ; assumption.
Qed.

Lemma Rplus_0_l (x : R) : 0 + x == x.
Proof.
  split ; intros q.
  - intros [r [s [H1 [H2 H3]]]].
    apply (lower_lower x q s) ; auto.
    transitivity (r+s)%Q;auto.
    apply (Qplus_lt_r _ _ (-s)); ring_simplify.
    apply H2.
  - intro H.
    destruct (lower_open x q H) as [r [G1 G2]].
    exists ((q - r) * (1#2))%Q, r ; split.
    + setoid_replace ((q - r) * (1 # 2) + r)%Q with ((q + r) * (1 # 2));[idtac|ring].
      apply (Qle_lt_trans q ((q+q)*(1#2))_); [ring_simplify; apply Qle_refl| idtac ].
      apply Qmult_lt_compat_r; [reflexivity | idtac].
      apply Qplus_lt_r; assumption.
    + split ; auto.
      cut ((q - r) * (1#2)<0)%Q;auto.
      apply (Qplus_lt_r _ _ (r*(1#2))); ring_simplify.
      setoid_replace ((1#2)*q) with (q*(1#2)); [idtac|ring].
      setoid_replace ((1#2)*r) with (r*(1#2)); [idtac|ring].
      apply Qmult_lt_compat_r; [reflexivity| assumption].
Qed.

Lemma Rplus_0_r (x : R) : x + 0 == x.
Proof.
  setoid_rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.

(** Properties of opposite. *)

Lemma Ropp_involutive (x : R) : - (- x) == x.
Proof.
  split ; intros q H ; simpl in * |- * ;
  rewrite Qopp_opp in * |- * ; assumption.
Qed.

Lemma Rplus_opp_r (x : R) : x + (- x) == 0.
Proof.
  split ; intros q H.
   - destruct H as [r [s [G1 [G2 G3]]]].
     apply (lower_lower 0 q (r + s)); auto.
     apply (Qplus_lt_r _ _ (-s)); ring_simplify.
     apply (lower_below_upper x); [assumption|auto].
  - assert (G : (-q > 0)%Q).
    + apply (Qplus_lt_r _ _ q) ; ring_simplify ; auto.
    + destruct (archimedean x _ G) as [a [b [A [B C]]]]. 
      exists a, (-b)%Q; repeat split; auto.
      apply (Qplus_lt_r _ _ (b-a-q)%Q) ; ring_simplify ; auto.
      cut (upper x (--b)) ; auto.
      rewrite Qopp_involutive; auto.
Qed.

Lemma Rplus_opp_l (x : R) : (- x) + x == 0.
Proof.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_plus_distr : forall r1 r2:R, - (r1 + r2) == - r1 + - r2.
Proof.
  split.
  - intros q [r [s H]]. exists (-r)%Q,(-s)%Q. simpl.
    repeat split. rewrite <- (Qplus_lt_l _ _ (r+s-q)). ring_simplify.
    setoid_replace (-1*q) with (-q)%Q. apply H. ring.
    apply (upper_proper r1 r). ring. apply H.
    apply (upper_proper r2 s). ring. apply H.
  - intros q [r [s H]]. exists (-r)%Q,(-s)%Q. 
    repeat split. rewrite <- (Qplus_lt_l _ _ (r+s+q)). ring_simplify.
    apply H. apply H. apply H.
Qed.

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros. destruct H as [q [u l]]. destruct u,H,H,l,H1,H1.
  assert (x + x0 < x1 + x2)%Q.
  { exact (Qlt_trans _ q _ H H1). }
  clear H1 H q.
  exists x0. split. apply H0.
  apply (lower_lower r2 x0 x2). 2: apply H2.
  rewrite <- (Qplus_lt_r _ _ x). apply (Qlt_trans _ (x1+x2) _ H3).
  rewrite Qplus_lt_l. apply (lower_below_upper r). apply H2. apply H0.
Qed.

Lemma Rplus_lt_reg_r : forall r r1 r2, r1 + r < r2 + r -> r1 < r2.
Proof.
  intros. rewrite Rplus_comm, (Rplus_comm r2) in H.
  apply (Rplus_lt_reg_l _ _ _ H).
Qed.

Lemma Rplus_le_compat_l : forall r r1 r2:R, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros. intros q [s [t H0]]. exists s, t.
  repeat split. apply H0. apply H0. apply H. apply H0.
Qed.

Lemma Rplus_le_compat_r : forall r r1 r2:R, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros. intros q [s [t H0]]. exists s, t.
  repeat split. apply H0. apply H. apply H0. apply H0.
Qed.

Lemma R_of_Q_plus : forall (q r : Q),
    R_of_Q (q + r) == R_of_Q q + R_of_Q r.
Proof.
  split.
  - intros a H. simpl. simpl in H.
    (* Improve q and r separately *)
    pose (((a-r)+q)*(1#2)) as q0.
    assert (a < q0 + r)%Q.
    { unfold q0. apply (Qplus_lt_l _ _ (-r)).
      rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
      apply middle_between. apply (Qplus_lt_r _ _ r).
      ring_simplify. rewrite Qplus_comm. exact H. }
    exists q0, (((a-q0)+r)*(1#2)). split.
    apply (Qplus_lt_l _ _ (-q0)).
    rewrite (Qplus_comm q0), <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
    apply middle_between. apply (Qplus_lt_r _ _ q0).
    ring_simplify. exact H0.
    split. apply middle_between.
    apply (Qplus_lt_r _ _ r). ring_simplify. rewrite Qplus_comm. exact H.
    apply middle_between. apply (Qplus_lt_r _ _ q0).
    ring_simplify. exact H0.
  - intros a H. destruct H as [s [t H]]. simpl.
    simpl in H. apply (Qlt_trans _ (s+t)). apply H.
    apply (Qplus_lt_le_compat). apply H.
    apply Qlt_le_weak. apply H.
Qed.
