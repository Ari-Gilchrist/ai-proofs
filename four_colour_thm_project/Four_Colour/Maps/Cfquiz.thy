(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfquiz.thy
    Compiling a configuration program into a quiz (cfquiz.v, definitions).
    Ported from G. Gonthier's Coq development (cfquiz.v).

    The correctness theorem of cfquiz.v (cfquizP / embeddable_cfquiz / valid_cfquiz) is NOT yet
    ported; it is recorded below as the predicate cfquiz_correct, which downstream theories take
    as an explicit hypothesis until it is discharged.
*)
theory Cfquiz
  imports Four_Colour_Maps.Quiz
begin

datatype ring_question = RingQuestion (rq_isk: bool) (rq_arity: nat) (rq_question: question)

definition small_qarity :: "nat \<Rightarrow> qarity" where
  "small_qarity a = (if a = 3 then Qa5 else if a = 4 then Qa6 else if a = 5 then Qa7
     else if a = 6 then Qa8 else if a = 7 then Qa10 else Qa9)"

fun bad_small_arity :: "qarity \<Rightarrow> bool" where
  "bad_small_arity Qa9 = True" | "bad_small_arity Qa10 = True" | "bad_small_arity Qa11 = True"
| "bad_small_arity _ = False"

lemma small_qarityP:
  "bad_small_arity (small_qarity a) \<longleftrightarrow> nat_of_qarity (small_qarity a) \<noteq> a + 2"
  by (simp add: small_qarity_def)

definition large_qarity :: "nat \<Rightarrow> qarity" where
  "large_qarity a = (if a = 7 then Qa9 else if a = 8 then Qa10 else if a = 9 then Qa11
     else small_qarity a)"

definition bad_ring_arity :: "nat \<Rightarrow> bool" where
  "bad_ring_arity a \<longleftrightarrow> a = 0 \<or> 5 \<le> a"

definition noquiz :: quiz where "noquiz = Quiz Qask0 Qask0"

fun rqs_Y :: "ring_question \<Rightarrow> ring_question \<Rightarrow> ring_question list \<Rightarrow> question \<Rightarrow>
    ring_question list" where
  "rqs_Y (RingQuestion k1 a1 _) (RingQuestion k3 a3 q3) qs q1' =
     RingQuestion k1 (Suc a1) q1' # RingQuestion k3 (Suc a3) q3 # qs"

fun cfquiz_Y :: "ring_question \<Rightarrow> ring_question \<Rightarrow> (question \<Rightarrow> ring_question list) \<Rightarrow>
    ring_question list" where
  "cfquiz_Y (RingQuestion _ _ q1) (RingQuestion k2 a2 q2) rqs' =
    (if k2 then
       (let qa2 = small_qarity a2 in
        if bad_small_arity qa2 then [] else
        rqs' (case (q1, q2) of
                (Qask0, Qask0) \<Rightarrow> Qask1 qa2
              | (Qask0, _) \<Rightarrow> QaskL qa2 q2
              | (_, Qask0) \<Rightarrow> QaskR qa2 q1
              | _ \<Rightarrow> QaskLR qa2 q2 q1))
     else if bad_ring_arity a2 then [] else
       (case (q1, q2) of
          (Qask0, Qask0) \<Rightarrow> rqs' Qask0
        | (QaskR qa1 q1r, Qask0) \<Rightarrow> rqs' (QaskRR qa1 q1r)
        | (Qask0, QaskL qa1 q1l) \<Rightarrow> rqs' (QaskLL qa1 q1l)
        | _ \<Rightarrow> []))"

fun rqs_H :: "ring_question \<Rightarrow> ring_question \<Rightarrow> ring_question list \<Rightarrow> question \<Rightarrow> question \<Rightarrow>
    ring_question list" where
  "rqs_H (RingQuestion k1 a1 _) (RingQuestion k3 a3 q3) qs q1' q2' =
     RingQuestion k1 (Suc a1) q1' # RingQuestion True 1 q2' # RingQuestion k3 (Suc a3) q3 # qs"

fun cfquiz_H :: "ring_question \<Rightarrow> ring_question \<Rightarrow> (question \<Rightarrow> question \<Rightarrow> ring_question list) \<Rightarrow>
    ring_question list" where
  "cfquiz_H (RingQuestion k1 _ q1) (RingQuestion k2 a2 q2) rqs' =
    (if k2 then
       (let qa2 = small_qarity (Suc a2) in
        if bad_small_arity qa2 then [] else
        (case (q1, q2, k1) of
           (Qask0, Qask0, True) \<Rightarrow> rqs' (Qask1 qa2) q2
         | (Qask0, Qask0, False) \<Rightarrow> rqs' q1 (Qask1 qa2)
         | (Qask0, _, _) \<Rightarrow> rqs' q1 (QaskL qa2 q2)
         | (_, Qask0, _) \<Rightarrow> rqs' (QaskR qa2 q1) q2
         | _ \<Rightarrow> []))
     else if bad_ring_arity (Suc a2) then [] else
       (case (q1, q2) of (Qask0, Qask0) \<Rightarrow> rqs' q1 q2 | _ \<Rightarrow> []))"

fun cfquiz_rec :: "ring_question list \<Rightarrow> cprog \<Rightarrow> quiz" where
  "cfquiz_rec (RingQuestion k1 a1 q1 # RingQuestion k2 a2 q2 # _) [] =
    (if \<not> (k1 \<and> k2) then noquiz else
     (let qa1 = large_qarity (a1 - 1); qa2 = small_qarity (a2 - 1) in
      if nat_of_qarity qa1 \<noteq> Suc a1 \<or> bad_small_arity qa2 then noquiz else
      Quiz (QaskR qa1 q2) (QaskR qa2 q1)))"
| "cfquiz_rec (rq1 # rq2 # rq3 # qs') (CpR n # cp') = cfquiz_rec (rotr n (rq1 # rq2 # rq3 # qs')) cp'"
| "cfquiz_rec (rq1 # rq2 # rq3 # qs') (CpY # cp') = cfquiz_rec (cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs')) cp'"
| "cfquiz_rec (rq1 # rq2 # rq3 # qs') (CpH # cp') = cfquiz_rec (cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs')) cp'"
| "cfquiz_rec _ _ = noquiz"

fun cpradius2 :: "cprog \<Rightarrow> nat \<Rightarrow> bool" where
  "cpradius2 cp 0 = False"
| "cpradius2 cp (Suc i) =
    (case cfmask1 cp i of Cfmask mr1 _ \<Rightarrow>
      (case cpadj (cfmask1 cp i) cp of Cfmask _ mk1 \<Rightarrow>
        (case cpadj (Cfmask mr1 mk1) cp of Cfmask _ mk2 \<Rightarrow>
          (if list_all id mk2 then True else cpradius2 cp i))))"

definition cfquiz :: "config \<Rightarrow> quiz" where
  "cfquiz cf = (let cp = cfprog cf in
     if cpradius2 cp (cpksize cp) then cfquiz_rec (replicate (cprsize cp) (RingQuestion False 0 Qask0)) cp
     else noquiz)"

text \<open>The correctness predicate corresponding to cfquiz.v: a configuration whose compiled quiz is
  well formed is embeddable, and the quiz is valid for it.  In Gonthier's development this is
  lemmas @{text embeddable_cfquiz} and @{text valid_cfquiz}.\<close>

definition cfquiz_correct :: "config \<Rightarrow> bool" where
  "cfquiz_correct cf \<longleftrightarrow> (isQuizR (cfquiz cf) \<longrightarrow>
     embeddable (cpG (cfprog cf)) (cfring cf) \<and>
     (\<exists>u. valid_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf) \<and> u \<in> darts (cpG (cfprog cf))))"

end
