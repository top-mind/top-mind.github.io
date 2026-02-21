From Stdlib Require Import PeanoNat Nat Lia.

Parameter N : nat.

Parameter good : nat -> bool.

Axiom prop1 : forall n1 n2, n1 >= N -> n2 > n1 ->
  good n1 = true -> good n2 = true ->
  good (n1 * n2) = false.

Axiom prop2 : forall n, n >= N ->
  good n = false ->
  good (1 + n) = true.

Lemma lemma1 : forall n1, n1 >= N -> exists n2, n2 >= n1 /\ good n2 = true.
Proof.
  intros.
  destruct (good n1) eqn:E.
  - exists n1; auto.
  - apply prop2 in E; auto.
    exists (1 + n1); auto.
Qed.

Definition good_even n := if good n then even n else odd n.

Lemma mean_value : forall f b n1 n2,
  n1 < n2 ->
  f n1 = b -> f n2 = negb b ->
  exists n3, n1 <= n3 /\ n3 < n2 /\ f n3 = b /\ f (S n3) = negb b.
Proof with try lia; try tauto.
  induction n2; try lia; intros.
  destruct (f n2) eqn:E, b; try (exists n2; repeat split; try lia; auto; fail).
  all: assert (n1 <> n2) by (intros Hc; subst; rewrite E in H0; discriminate).
  all: destruct IHn2...
  all: exists x; repeat split...
Qed.

Ltac make_false H1 H2 H :=
  match type of H1 with
  | good ?n1 = true =>
    match type of H2 with
    | good ?n2 = true =>
      assert (H: good (n1 * n2) = false) by (apply prop1; auto; lia)
    end
  end.

Ltac make_true H1 H2 H Ht :=
    make_false H1 H2 Ht;
    match type of Ht with
    | good ?n = false =>
      assert (H: good (1 + n) = true);
      try (apply prop2; auto; try lia)
    end; clear Ht.

Ltac take H n0 :=
  match type of H with
  | good ?n = _ => remember n as n0
  end.

Lemma lemma2 : exists n, n > N /\ good n = true /\ good (1 + n) = true.
Proof with auto; try lia.
  destruct (lemma1 (1 + N)) as [n1 [? Hn1]]...
  destruct (good (1 + n1)) eqn:?H.
  - exists n1...
  - apply prop2 in H0...
    make_true Hn1 H0 H1 U.
    take H1 n2.
    destruct (mean_value good_even (even n1) n1 n2) as [n3 [? [_ [? ?]]]]
    ; unfold good_even in *;
      try rewrite Hn1; try rewrite H1...
    subst. rewrite Nat.even_succ, Nat.odd_mul, Nat.odd_succ_succ, Nat.negb_even.
    destruct (odd n1)...
    destruct (good n3) eqn:E.
    + exists n3. repeat split... simpl.
      destruct (good (S n3))...
      rewrite Nat.odd_succ, H3 in H4.
      destruct (even n1)...
    + apply prop2 in E... simpl in E.
      rewrite E in H4. rewrite Nat.even_succ, H3 in H4.
      destruct (even n1)...
Qed.

Theorem main : False.
Proof with auto; try lia.
  destruct lemma2 as [n1 [? [Hn1 HSn1]]].
  destruct (lemma1 (2 + n1)) as [n2 [? Hn2]]...
  make_true Hn1 Hn2 H1 U. destruct n2...
  make_true HSn1 Hn2 H2 U.
  make_false Hn1 H2 H3.
  assert (H4: good ((1 + n1) * (1 + n1 * n2)) = false).
  {
    apply prop1; destruct n1...
  }
  take H3 n3. take H4 n4.
  replace n4 with (1 + n3) in H4...
  apply prop2 in H3...
  rewrite H3 in H4. discriminate.
Qed.