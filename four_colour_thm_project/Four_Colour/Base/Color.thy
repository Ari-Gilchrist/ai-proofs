(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Color.thy
    The four colours, colour sums, edge permutations and edge traces.
    Ported from G. Gonthier's Coq development (color.v).
*)
theory Color
  imports FC_Seq
begin

section \<open>Colours\<close>

datatype color = Color0 | Color1 | Color2 | Color3

fun addc :: "color \<Rightarrow> color \<Rightarrow> color" (infixl "+c" 65) where
  "Color0 +c c = c"
| "Color1 +c Color0 = Color1" | "Color1 +c Color1 = Color0"
| "Color1 +c Color2 = Color3" | "Color1 +c Color3 = Color2"
| "Color2 +c Color0 = Color2" | "Color2 +c Color1 = Color3"
| "Color2 +c Color2 = Color0" | "Color2 +c Color3 = Color1"
| "Color3 +c Color0 = Color3" | "Color3 +c Color1 = Color2"
| "Color3 +c Color2 = Color1" | "Color3 +c Color3 = Color0"

lemma color_all: "(\<forall>c. P c) \<longleftrightarrow> P Color0 \<and> P Color1 \<and> P Color2 \<and> P Color3"
  by (metis color.exhaust)

lemma color_ex: "(\<exists>c. P c) \<longleftrightarrow> P Color0 \<or> P Color1 \<or> P Color2 \<or> P Color3"
  by (metis color.exhaust)

lemma UNIV_color: "UNIV = {Color0, Color1, Color2, Color3}"
  by (auto intro: color.exhaust)

instance color :: finite
  by standard (simp add: UNIV_color)

lemma addcA: "(a +c b) +c c = a +c (b +c c)"
  by (cases a; cases b; cases c) simp_all

lemma addcC: "a +c b = b +c a"
  by (cases a; cases b) simp_all

lemma add0c [simp]: "Color0 +c c = c"
  by simp

lemma addc0 [simp]: "c +c Color0 = c"
  by (cases c) simp_all

lemma addcc [simp]: "c +c c = Color0"
  by (cases c) simp_all

lemma addKc [simp]: "a +c (a +c b) = b"
  by (cases a; cases b) simp_all

lemma addcK [simp]: "(b +c a) +c a = b"
  by (cases a; cases b) simp_all

lemma addcI: "a +c b = a +c c \<longleftrightarrow> b = c"
  by (metis addKc)

lemma addc_eq0: "a +c b = Color0 \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

section \<open>Colours as bit vectors\<close>

fun cbit0 :: "color \<Rightarrow> bool" where
  "cbit0 Color0 = False" | "cbit0 Color1 = True" | "cbit0 Color2 = False" | "cbit0 Color3 = True"

fun cbit1 :: "color \<Rightarrow> bool" where
  "cbit1 Color0 = False" | "cbit1 Color1 = False" | "cbit1 Color2 = True" | "cbit1 Color3 = True"

fun ccons :: "bool \<Rightarrow> bool \<Rightarrow> color" where
  "ccons False False = Color0" | "ccons False True = Color1"
| "ccons True False = Color2" | "ccons True True = Color3"

lemma ccons_cbits [simp]: "ccons (cbit1 c) (cbit0 c) = c"
  by (cases c) simp_all

lemma cbit1_ccons [simp]: "cbit1 (ccons b1 b0) = b1"
  by (cases b1; cases b0) simp_all

lemma cbit0_ccons [simp]: "cbit0 (ccons b1 b0) = b0"
  by (cases b1; cases b0) simp_all

lemma cbit1_addc: "cbit1 (a +c b) = (cbit1 a \<noteq> cbit1 b)"
  by (cases a; cases b) simp_all

lemma cbit0_addc: "cbit0 (a +c b) = (cbit0 a \<noteq> cbit0 b)"
  by (cases a; cases b) simp_all

section \<open>Edge permutations\<close>

datatype edge_perm = Eperm123 | Eperm132 | Eperm213 | Eperm231 | Eperm312 | Eperm321

fun permc :: "edge_perm \<Rightarrow> color \<Rightarrow> color" where
  "permc Eperm123 c = c"
| "permc Eperm132 Color0 = Color0" | "permc Eperm132 Color1 = Color1"
| "permc Eperm132 Color2 = Color3" | "permc Eperm132 Color3 = Color2"
| "permc Eperm213 Color0 = Color0" | "permc Eperm213 Color1 = Color2"
| "permc Eperm213 Color2 = Color1" | "permc Eperm213 Color3 = Color3"
| "permc Eperm231 Color0 = Color0" | "permc Eperm231 Color1 = Color2"
| "permc Eperm231 Color2 = Color3" | "permc Eperm231 Color3 = Color1"
| "permc Eperm312 Color0 = Color0" | "permc Eperm312 Color1 = Color3"
| "permc Eperm312 Color2 = Color1" | "permc Eperm312 Color3 = Color2"
| "permc Eperm321 Color0 = Color0" | "permc Eperm321 Color1 = Color3"
| "permc Eperm321 Color2 = Color2" | "permc Eperm321 Color3 = Color1"

fun inv_eperm :: "edge_perm \<Rightarrow> edge_perm" where
  "inv_eperm Eperm312 = Eperm231"
| "inv_eperm Eperm231 = Eperm312"
| "inv_eperm g = g"

lemma inv_epermK [simp]: "inv_eperm (inv_eperm g) = g"
  by (cases g) simp_all

lemma inv_permc [simp]: "permc (inv_eperm g) (permc g c) = c"
  by (cases g; cases c) simp_all

lemma permc_inv [simp]: "permc g (permc (inv_eperm g) c) = c"
  by (cases g; cases c) simp_all

lemma permc_inj: "permc g a = permc g b \<longleftrightarrow> a = b"
  by (metis inv_permc)

lemma permc_addc: "permc g (a +c b) = permc g a +c permc g b"
  by (cases g; cases a; cases b) simp_all

lemma permc0 [simp]: "permc g Color0 = Color0"
  by (cases g) simp_all

lemma permc_eq0 [simp]: "permc g c = Color0 \<longleftrightarrow> c = Color0"
  by (cases g; cases c) simp_all

lemma color_inj_permc:
  assumes "inj f" "f Color0 = Color0"
  shows "\<exists>g. \<forall>c. f c = permc g c"
proof -
  have d: "f a = f b \<longleftrightarrow> a = b" for a b using assms(1) by (simp add: inj_eq)
  have "f Color1 \<noteq> Color0" "f Color2 \<noteq> Color0" "f Color3 \<noteq> Color0"
    using d[of _ Color0] assms(2) by auto
  moreover have "f Color1 \<noteq> f Color2" "f Color1 \<noteq> f Color3" "f Color2 \<noteq> f Color3"
    using d by auto
  ultimately show ?thesis using assms(2)
    apply (cases "f Color1"; cases "f Color2"; cases "f Color3"; simp)
    by (metis color.exhaust permc.simps)+
qed

section \<open>Traces\<close>

type_synonym colseq = "color list"

definition head_color :: "colseq \<Rightarrow> color" where
  "head_color et = (case et of [] \<Rightarrow> Color0 | c # _ \<Rightarrow> c)"

definition proper_trace :: "colseq \<Rightarrow> bool" where
  "proper_trace et \<longleftrightarrow> head_color et \<noteq> Color0"

definition ptrace :: "colseq \<Rightarrow> colseq" where
  "ptrace lc = (case lc of [] \<Rightarrow> [] | c # lc' \<Rightarrow> pairmap addc c lc')"

definition permt :: "edge_perm \<Rightarrow> colseq \<Rightarrow> colseq" where
  "permt g = map (permc g)"

definition sumt :: "colseq \<Rightarrow> color" where
  "sumt et = foldr addc et Color0"

definition ctrace :: "colseq \<Rightarrow> colseq" where
  "ctrace et = et @ [sumt et]"

definition trace :: "colseq \<Rightarrow> colseq" where
  "trace lc = (case lc of [] \<Rightarrow> [] | _ \<Rightarrow> ctrace (ptrace lc))"

definition urtrace :: "colseq \<Rightarrow> colseq" where
  "urtrace lc = pairmap addc (if lc = [] then Color0 else last lc) lc"

definition untrace :: "color \<Rightarrow> colseq \<Rightarrow> colseq" where
  "untrace c0 et = scanl' addc c0 (butlast (Color0 # et))"

fun edge_rot :: "color \<Rightarrow> edge_perm" where
  "edge_rot Color0 = Eperm123" | "edge_rot Color1 = Eperm123"
| "edge_rot Color2 = Eperm312" | "edge_rot Color3 = Eperm231"

definition ttail :: "colseq \<Rightarrow> colseq" where
  "ttail et = (if proper_trace et then (case et of c # et' \<Rightarrow> permt (edge_rot c) et' | [] \<Rightarrow> [])
               else [Color0])"

fun even_tail :: "colseq \<Rightarrow> bool" where
  "even_tail [] = True"
| "even_tail (c # et) = (case c of Color2 \<Rightarrow> True | Color3 \<Rightarrow> False | _ \<Rightarrow> even_tail et)"

definition even_trace :: "colseq \<Rightarrow> bool" where
  "even_trace et = even_tail (ttail et)"

definition etrace_perm :: "colseq \<Rightarrow> edge_perm" where
  "etrace_perm et = (if even_trace et then Eperm123 else Eperm132)"

definition etrace :: "colseq \<Rightarrow> colseq" where
  "etrace et = permt (etrace_perm et) et"

definition etail :: "colseq \<Rightarrow> colseq" where
  "etail et = permt (etrace_perm et) (ttail et)"

definition eptrace :: "colseq \<Rightarrow> colseq" where
  "eptrace lc = etail (ptrace lc)"

fun count_cbit1 :: "colseq \<Rightarrow> nat" where
  "count_cbit1 [] = 0"
| "count_cbit1 (c # et) = (if cbit1 c then 1 else 0) + count_cbit1 et"

section \<open>Trace lemmas\<close>

lemma permt_id [simp]: "permt Eperm123 et = et"
  by (induction et) (simp_all add: permt_def)

lemma permt_132_twice [simp]: "permt Eperm132 (permt Eperm132 et) = et"
proof -
  have "permc Eperm132 (permc Eperm132 c) = c" for c by (cases c) simp_all
  then show ?thesis by (induction et) (simp_all add: permt_def)
qed

lemma permc_eq0' [simp]: "Color0 = permc g c \<longleftrightarrow> c = Color0"
  by (cases g; cases c) simp_all

lemma memc0_permt [simp]: "Color0 \<in> set (permt g et) \<longleftrightarrow> Color0 \<in> set et"
  by (induction et) (auto simp: permt_def)

lemma proper_permt [simp]: "proper_trace (permt g et) = proper_trace et"
  by (cases et) (simp_all add: proper_trace_def head_color_def permt_def)

lemma length_permt [simp]: "length (permt g et) = length et"
  by (simp add: permt_def)

lemma permt_append: "permt g (a @ b) = permt g a @ permt g b"
  by (simp add: permt_def)

lemma permt_Cons [simp]: "permt g (c # et) = permc g c # permt g et"
  by (simp add: permt_def)

lemma permt_Nil [simp]: "permt g [] = []"
  by (simp add: permt_def)

lemma memc0_ttail:
  "Color0 \<in> set (ttail et) \<longleftrightarrow> \<not> proper_trace et \<or> Color0 \<in> set et"
  by (cases et) (auto simp: ttail_def proper_trace_def head_color_def)

lemma even_etail: "even_tail (etail et)"
proof (cases "even_trace et")
  case True
  then show ?thesis by (simp add: etail_def etrace_perm_def even_trace_def)
next
  case False
  then have "\<not> even_tail (ttail et)" by (simp add: even_trace_def)
  moreover have "\<not> even_tail l \<Longrightarrow> even_tail (permt Eperm132 l)" for l
    by (induction l) (auto split: color.splits)
  ultimately show ?thesis using False by (simp add: etail_def etrace_perm_def)
qed

lemma compose_permt: "\<exists>h. permt h et = permt g (permt g' et)"
proof -
  have "inj (permc g \<circ> permc g')" by (auto simp: inj_def permc_inj)
  moreover have "(permc g \<circ> permc g') Color0 = Color0" by simp
  ultimately obtain h where h: "\<forall>c. (permc g \<circ> permc g') c = permc h c"
    using color_inj_permc by blast
  then have "permt h et = permt g (permt g' et)"
    by (induction et) (simp_all add: permt_def)
  then show ?thesis by blast
qed

lemma sumt_Cons [simp]: "sumt (c # et) = c +c sumt et"
  by (simp add: sumt_def)

lemma sumt_Nil [simp]: "sumt [] = Color0"
  by (simp add: sumt_def)

lemma sumt_append: "sumt (a @ b) = sumt a +c sumt b"
  by (induction a) (simp_all add: addcA)

lemma sumt_ctrace [simp]: "sumt (ctrace et) = Color0"
  by (simp add: ctrace_def sumt_append)

lemma sumt_permt: "sumt (permt g et) = permc g (sumt et)"
  by (induction et) (simp_all add: permc_addc)

lemma ctrace_permt: "ctrace (permt g et) = permt g (ctrace et)"
  by (simp add: ctrace_def sumt_permt permt_append)

lemma proper_ctrace [simp]: "proper_trace (ctrace et) = proper_trace et"
  by (cases et) (simp_all add: ctrace_def proper_trace_def head_color_def)

lemma ctrace_inj: "ctrace a = ctrace b \<longleftrightarrow> a = b"
proof
  assume "ctrace a = ctrace b"
  then have "butlast (ctrace a) = butlast (ctrace b)" by simp
  then show "a = b" by (simp add: ctrace_def)
qed simp

lemma length_ptrace [simp]: "length (ptrace lc) = length lc - 1"
  by (cases lc) (simp_all add: ptrace_def)

lemma ptrace_permt: "ptrace (permt g lc) = permt g (ptrace lc)"
proof (cases lc)
  case Nil
  then show ?thesis by (simp add: ptrace_def)
next
  case (Cons c l)
  have "pairmap addc (permc g c) (map (permc g) l) = map (permc g) (pairmap addc c l)" for c
    by (induction l arbitrary: c) (simp_all add: permc_addc)
  then show ?thesis using Cons by (simp add: ptrace_def permt_def)
qed

lemma ptrace_addc: "ptrace (map (addc c) lc) = ptrace lc"
proof (cases lc)
  case Nil
  then show ?thesis by (simp add: ptrace_def)
next
  case (Cons d l)
  have "pairmap addc (c +c d) (map (addc c) l) = pairmap addc d l" for d
  proof (induction l arbitrary: d)
    case Nil
    then show ?case by simp
  next
    case (Cons x l)
    have "(c +c d) +c (c +c x) = d +c x"
      by (cases c; cases d; cases x) simp_all
    then show ?case using Cons by simp
  qed
  then show ?thesis using Cons by (simp add: ptrace_def)
qed

lemma length_trace [simp]: "length (trace lc) = length lc"
  by (cases lc) (simp_all add: trace_def ctrace_def ptrace_def)

lemma sumt_trace [simp]: "sumt (trace lc) = Color0"
  by (cases lc) (simp_all add: trace_def)

lemma trace_alt: "lc \<noteq> [] \<Longrightarrow> trace lc = ctrace (ptrace lc)"
  by (cases lc) (simp_all add: trace_def)

lemma trace_permt: "trace (permt g lc) = permt g (trace lc)"
proof (cases "lc = []")
  case True
  then show ?thesis by (simp add: trace_def)
next
  case False
  then have "permt g lc \<noteq> []" by (simp add: permt_def)
  then show ?thesis
    using trace_alt[OF False] trace_alt[of "permt g lc"] ptrace_permt[of g lc] ctrace_permt by simp
qed

lemma trace_addc: "trace (map (addc c) lc) = trace lc"
proof (cases "lc = []")
  case True
  then show ?thesis by (simp add: trace_def)
next
  case False
  then have "map (addc c) lc \<noteq> []" by simp
  then show ?thesis
    using trace_alt[OF False] trace_alt[of "map (addc c) lc"] ptrace_addc[of c lc] by simp
qed

lemma pairmap_snoc: "pairmap f x (l @ [y]) = pairmap f x l @ [f (last (x # l)) y]"
  by (induction l arbitrary: x) simp_all

lemma sumt_pairmap: "sumt (pairmap addc c l) = c +c last (c # l)"
  by (induction l arbitrary: c) (simp_all, metis addcA addcK addcC)

lemma trace_Cons: "trace (c # lc) = pairmap addc c (lc @ [c])"
proof -
  have "trace (c # lc) = pairmap addc c lc @ [c +c last (c # lc)]"
    by (simp add: trace_def ptrace_def ctrace_def sumt_pairmap)
  also have "\<dots> = pairmap addc c (lc @ [c])"
    by (simp add: pairmap_snoc addcC)
  finally show ?thesis .
qed

lemma even_ctrace: "even_trace (ctrace et) = even_trace et"
proof (cases et)
  case Nil
  then show ?thesis by (simp add: even_trace_def ctrace_def ttail_def proper_trace_def head_color_def)
next
  case (Cons e et')
  show ?thesis
  proof (cases "e = Color0")
    case True
    then show ?thesis using Cons
      by (simp add: even_trace_def ctrace_def ttail_def proper_trace_def head_color_def)
  next
    case False
    let ?g = "edge_rot e"
    have ge: "\<not> cbit1 (permc ?g e)" using False by (cases e) simp_all
    have key: "\<not> cbit1 (permc g d) \<Longrightarrow>
       even_tail (permt g (l @ [d +c sumt l])) = even_tail (permt g l)" for g d l
    proof (induction l arbitrary: d)
      case Nil
      then show ?case by (cases "permc g d") simp_all
    next
      case (Cons x l)
      show ?case
      proof (cases "permc g x")
        case Color0
        then have "x = Color0" by simp
        then show ?thesis using Cons by simp
      next
        case Color1
        have "\<not> cbit1 (permc g (d +c x))"
          using Cons.prems Color1 by (simp add: permc_addc cbit1_addc)
        then have "even_tail (permt g (l @ [(d +c x) +c sumt l])) = even_tail (permt g l)"
          by (rule Cons.IH)
        then show ?thesis using Color1 by (simp add: addcA)
      qed simp_all
    qed
    have "even_tail (permt ?g (et' @ [e +c sumt et'])) = even_tail (permt ?g et')"
      by (rule key[OF ge])
    then show ?thesis using Cons False
      by (simp add: even_trace_def ctrace_def ttail_def proper_trace_def head_color_def)
  qed
qed

lemma trace_untrace: "sumt et = Color0 \<Longrightarrow> trace (untrace c0 et) = et"
proof -
  assume s: "sumt et = Color0"
  show ?thesis
  proof (cases et)
    case Nil
    then show ?thesis by (simp add: untrace_def trace_def)
  next
    case (Cons e1 et')
    have A: "pairmap addc c (scanl' addc c l) = l" for c l
      by (induction l arbitrary: c) (simp_all add: addcA[symmetric])
    have B: "sumt (butlast (e1 # et')) +c sumt [last (e1 # et')] = Color0"
      using s Cons by (metis append_butlast_last_id list.distinct(1) sumt_append addc0 sumt_Cons sumt_Nil)
    have "untrace c0 et = c0 # scanl' addc c0 (butlast (e1 # et'))"
      using Cons by (simp add: untrace_def)
    then have "ptrace (untrace c0 et) = butlast (e1 # et')"
      by (simp add: ptrace_def A)
    moreover have "sumt (butlast (e1 # et')) = last (e1 # et')"
      using B by (simp add: addc_eq0)
    ultimately show ?thesis using Cons
      by (simp add: trace_def ctrace_def untrace_def)
  qed
qed

lemma untrace_trace: "untrace c0 (trace (c0 # lc)) = c0 # lc"
proof -
  have A: "scanl' addc c (pairmap addc c l) = l" for c l
    by (induction l arbitrary: c) simp_all
  have "butlast (Color0 # trace (c0 # lc)) = Color0 # pairmap addc c0 lc"
    by (simp add: trace_def ptrace_def ctrace_def)
  then show ?thesis by (simp add: untrace_def A)
qed

end
