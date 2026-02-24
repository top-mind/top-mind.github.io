(** misc.v v0.2 
 * Problem: prove that there is no way to partition the integers greater than
   or equal to 2025 into good numbers and bad numbers such that the product of
   any two distinct good numbers is a bad number, and no two bad numbers are
   adjacent.
   不存在一种方案，能把 >= 2025 的整数划分为好数和坏数，使得任意两个不同好数之积是坏数，且任意两个坏数不相邻。
 * This is a secondary-school-level problem from Baidu tieba (https://tieba.baidu.com/p/10161855656?share=9105&fr=sharewise&see_lz=0&share_from=post&sfc=copy&client_type=2&client_version=22.1.1.0&st=1771952252&is_video=false&unique=A7FBBC8EC8C1076BA0066660C62B9669)
   Due 2026/2/24, there is no LLM other than GPT-5.2(xhigh) and Gemini 3 Pro that can solve this problem
   (i've not tested Claude Opus 4.6).
   Deepseek 3.2 Speciale, Qwen 3.5 Plus, GLM 5, Kimi K2.5 failed.
 * This is a more clever proof inspired by Gemini 3.1 pro
 *)

From Stdlib Require Import Lia.

Parameter N : nat.

Parameter good : nat -> bool.

Axiom prop1 : forall n1 n2, n1 >= N -> n2 > n1 ->
  good n1 = true -> good n2 = true ->
  good (n1 * n2) = false.

Axiom prop2 : forall n, n >= N ->
  good n = false ->
  good (1 + n) = true.

Ltac make_true n1 n2 :=
  assert (good (1+n1*n2) = true) by (apply prop2; auto; try nia; apply prop1; auto; try nia).

Ltac make_false n1 n2 :=
  assert (good (n1*n2) = false) by (apply prop1; auto; try nia).

Lemma lemma1 : forall n, n > N -> good n = true -> good (S n) = false.
Proof with auto; try lia.
  intros.
  destruct (good (S n)) eqn:GS... exfalso.
  destruct (good (S (S n))) eqn:GSS.
  1: remember (S (S n)) as m.
  2: assert (HH:good (1+S (S n)) = true) by (apply prop2; auto; lia);
     remember (1 + S (S n)) as m.
  all: make_true n m;
    make_true (S n) m;
    make_false n (1+S n*m);
    make_false (S n) (1+n*m);
    assert (false = true) by (
      rewrite <-H4; replace (S n * (1 + n * m)) with (1+(n * (1 + S n * m))) by lia;
      apply prop2; auto; lia
    );
    congruence.
Qed.

Lemma lemma2 : (forall n, n > N -> good n = true -> good (S n) = false) -> False.
Proof with auto; try lia.
  intros H.
  assert (forall i n, n > N -> good n = true -> good (i + i + n) = true).
  {
    induction i; intros; auto.
    replace (S i + S i + n) with (2 + (i + i + n)) by lia.
    apply prop2...
    apply H...
  }
  remember (1 + N) as M.
  destruct (good (2 * M)) eqn:GN.
  - assert (good (1 + 1 + 2 * M) = true). { apply H0... }
    make_false (2 * M) (2 + 2 * M).
    assert (false = true). {
      rewrite <-H2.
      replace (2 * M * (2 + 2 * M)) with (M*(2*M+1)+M*(2*M+1)+2*M) by lia.
      apply H0...
    } congruence.
  - assert (good (1 + 2 * M) = true). { apply prop2... }
    assert (good (1 + 1 + (1 + 2 * M)) = true). { apply H0... }
    make_false (1 + 2 * M) (1 + 1 + (1 + 2 * M)).
    assert (false = true). {
      rewrite <-H3.
      replace ((1 + 2 * M) * (1 + 1 + (1 + 2 * M))) with
      ((M+1)*(2*M+1)+(M+1)*(2*M+1)+(1+2*M)) by lia.
      apply H0...
    } congruence.
Qed.

Theorem main : False.
Proof.
  apply lemma2, lemma1.
Qed.
