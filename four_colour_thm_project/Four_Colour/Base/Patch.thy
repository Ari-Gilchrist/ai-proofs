(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Patch.thy
    Patching two maps along a ring to cover a larger one.
    Ported from G. Gonthier's Coq development (patch.v).
*)
theory Patch
  imports Mincex Cube
begin

text \<open>
  @{term "patch G Gd Gr hd hr bGd bGr"}: the hypermap @{term G} is obtained by
  glueing the ``disk'' map @{term Gd} and the ``remainder'' map @{term Gr} along
  the simple edge cycle @{term bGd} of @{term Gd} and the node cycle @{term bGr}
  of @{term Gr}.  The dart types of the three maps may differ.
\<close>

section \<open>More trace lemmas\<close>

lemma pairmap_nth: "i < length l \<Longrightarrow> pairmap f x l ! i = f ((x # l) ! i) (l ! i)"
proof (induction l arbitrary: x i)
  case Nil
  then show ?case by simp
next
  case (Cons y l)
  then show ?case by (cases i) auto
qed

lemma trace_nth:
  assumes i: "i < length lc"
  shows "trace lc ! i = lc ! i +c lc ! (Suc i mod length lc)"
proof (cases lc)
  case Nil
  then show ?thesis using i by simp
next
  case (Cons c l)
  have tr: "trace lc = pairmap addc c (l @ [c])" using Cons by (simp add: trace_Cons)
  have il: "i < length (l @ [c])" using i Cons by simp
  have "trace lc ! i = (c # l @ [c]) ! i +c (l @ [c]) ! i" using tr pairmap_nth[OF il] by simp
  moreover have "(c # l @ [c]) ! i = lc ! i"
    using i Cons by (simp add: nth_append nth_Cons split: nat.splits)
  moreover have "(l @ [c]) ! i = lc ! (Suc i mod length lc)"
  proof (cases "i < length l")
    case True
    then show ?thesis using Cons by (simp add: nth_append)
  next
    case False
    then have "i = length l" using i Cons by simp
    then show ?thesis using Cons by simp
  qed
  ultimately show ?thesis by simp
qed

lemma rot1_nth:
  assumes i: "i < length s"
  shows "rot 1 s ! i = s ! (Suc i mod length s)"
proof (cases s)
  case Nil
  then show ?thesis using i by simp
next
  case (Cons a t)
  have r: "rot 1 s = t @ [a]" using Cons rot1_Cons[of a t] by simp
  show ?thesis
  proof (cases "i < length t")
    case True
    then show ?thesis using r Cons by (simp add: nth_append)
  next
    case False
    then have "i = length t" using i Cons by simp
    then show ?thesis using r Cons by simp
  qed
qed

lemma trace_rev: "trace (rev lc) = rot 1 (rev (trace lc))"
proof (rule nth_equalityI)
  show "length (trace (rev lc)) = length (rot 1 (rev (trace lc)))" by simp
next
  fix i assume i: "i < length (trace (rev lc))"
  define n where "n = length lc"
  have in_: "i < n" using i by (simp add: n_def)
  have n0: "0 < n" using in_ by simp
  have t1: "trace (rev lc) ! i = rev lc ! i +c rev lc ! (Suc i mod n)"
    using trace_nth[of i "rev lc"] in_ by (simp add: n_def)
  have t2: "rev lc ! i = lc ! (n - 1 - i)" using in_ by (simp add: rev_nth n_def)
  have smn: "Suc i mod n < n" using n0 by simp
  have t3: "rev lc ! (Suc i mod n) = lc ! (n - 1 - Suc i mod n)"
    using smn by (simp add: rev_nth n_def)
  have L: "trace (rev lc) ! i = lc ! (n - 1 - i) +c lc ! (n - 1 - Suc i mod n)"
    using t1 t2 t3 by simp
  define m where "m = n - 1 - Suc i mod n"
  have mn: "m < n" using n0 by (simp add: m_def)
  have sm: "Suc m mod n = n - 1 - i"
  proof (cases "Suc i < n")
    case True
    then have "Suc i mod n = Suc i" by simp
    then have "m = n - 2 - i" by (simp add: m_def)
    then show ?thesis using True by simp
  next
    case False
    then have "Suc i = n" using in_ by simp
    then show ?thesis using n0 by (simp add: m_def)
  qed
  have R: "rot 1 (rev (trace lc)) ! i = lc ! m +c lc ! (Suc m mod n)"
  proof -
    have "rot 1 (rev (trace lc)) ! i = rev (trace lc) ! (Suc i mod n)"
      using rot1_nth[of i "rev (trace lc)"] in_ by (simp add: n_def)
    also have "\<dots> = trace lc ! m"
      using n0 by (simp add: rev_nth m_def n_def)
    also have "\<dots> = lc ! m +c lc ! (Suc m mod n)" using trace_nth[of m lc] mn by (simp add: n_def)
    finally show ?thesis .
  qed
  show "trace (rev lc) ! i = rot 1 (rev (trace lc)) ! i"
    using L R sm by (simp add: m_def addcC)
qed

lemma scanl'_addc_shift: "scanl' addc (c +c d) l = map (addc d) (scanl' addc c l)"
proof (induction l arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons x l)
  have "(c +c d) +c x = d +c (c +c x)" by (cases c; cases d; cases x) simp_all
  moreover have "scanl' addc ((c +c x) +c d) l = map (addc d) (scanl' addc (c +c x) l)" by (rule Cons.IH)
  moreover have "(c +c x) +c d = (c +c d) +c x" by (metis addcA addcC)
  ultimately show ?case by simp
qed

lemma trace_eq_shift:
  assumes t: "trace l1 = trace l2" and l: "l1 \<noteq> []" "l2 \<noteq> []"
  shows "l1 = map (addc (hd l1 +c hd l2)) l2"
proof -
  obtain c1 r1 where l1: "l1 = c1 # r1" using l(1) by (cases l1) auto
  obtain c2 r2 where l2: "l2 = c2 # r2" using l(2) by (cases l2) auto
  have "l1 = untrace c1 (trace l1)" using l1 untrace_trace by simp
  also have "\<dots> = untrace c1 (trace l2)" using t by simp
  also have "untrace c1 (trace l2) = map (addc (c1 +c c2)) (untrace c2 (trace l2))"
  proof -
    have "c1 = c2 +c (c1 +c c2)" by (cases c1; cases c2) simp_all
    then show ?thesis unfolding untrace_def by (metis scanl'_addc_shift addcC)
  qed
  also have "untrace c2 (trace l2) = l2" using l2 untrace_trace by simp
  finally show ?thesis using l1 l2 by simp
qed

section \<open>Cyclic successors in lists\<close>

lemma nth_mod_mem: "p \<noteq> [] \<Longrightarrow> p ! (k mod length p) \<in> set p"
proof -
  assume "p \<noteq> []"
  then have "k mod length p < length p" by simp
  then show ?thesis by (rule nth_mem)
qed

lemma next_in_mem: "x \<in> set p \<Longrightarrow> next_in p x \<in> set p"
proof -
  assume x: "x \<in> set p"
  then have "p \<noteq> []" by auto
  then show ?thesis using x nth_mod_mem[of p "Suc (lindex p x)"] by (simp add: next_in_def)
qed

lemma prev_in_mem: "x \<in> set p \<Longrightarrow> prev_in p x \<in> set p"
proof -
  assume x: "x \<in> set p"
  then have "p \<noteq> []" by auto
  then show ?thesis using x nth_mod_mem[of p "lindex p x + length p - 1"] by (simp add: prev_in_def)
qed

lemma next_in_lindex:
  assumes d: "distinct p" and x: "x \<in> set p"
  shows "lindex p (next_in p x) = Suc (lindex p x) mod length p"
proof -
  have "p \<noteq> []" using x by auto
  then have "Suc (lindex p x) mod length p < length p" by simp
  then show ?thesis using x d by (simp add: next_in_def lindex_nth_distinct)
qed

lemma prev_next_in: "distinct p \<Longrightarrow> x \<in> set p \<Longrightarrow> prev_in p (next_in p x) = x"
proof -
  assume d: "distinct p" and x: "x \<in> set p"
  define i where "i = lindex p x"
  define L where "L = length p"
  have iL: "i < L" unfolding i_def L_def by (rule lindex_less[OF x])
  have xi: "p ! i = x" unfolding i_def by (rule nth_lindex[OF x])
  have nx: "next_in p x \<in> set p" by (rule next_in_mem[OF x])
  have li: "lindex p (next_in p x) = Suc i mod L" unfolding i_def L_def by (rule next_in_lindex[OF d x])
  have "(Suc i mod L + L - 1) mod L = i"
  proof (cases "Suc i < L")
    case True
    then show ?thesis using iL by simp
  next
    case False
    then have "Suc i = L" using iL by simp
    then show ?thesis by simp
  qed
  then show ?thesis using nx li xi by (simp add: prev_in_def L_def)
qed

lemma next_prev_in: "distinct p \<Longrightarrow> x \<in> set p \<Longrightarrow> next_in p (prev_in p x) = x"
proof -
  assume d: "distinct p" and x: "x \<in> set p"
  define i where "i = lindex p x"
  define L where "L = length p"
  have iL: "i < L" unfolding i_def L_def by (rule lindex_less[OF x])
  have xi: "p ! i = x" unfolding i_def by (rule nth_lindex[OF x])
  have L0: "L > 0" using iL by simp
  have j: "(i + L - 1) mod L < L" using L0 by simp
  have px: "prev_in p x = p ! ((i + L - 1) mod L)" using x by (simp add: prev_in_def i_def L_def)
  have pm: "prev_in p x \<in> set p" by (rule prev_in_mem[OF x])
  have lj: "lindex p (prev_in p x) = (i + L - 1) mod L"
    using px j d by (simp add: lindex_nth_distinct L_def)
  have "Suc ((i + L - 1) mod L) mod L = i"
  proof (cases "i = 0")
    case True
    then show ?thesis using L0 by (simp add: mod_Suc)
  next
    case False
    then have "(i + L - 1) mod L = i - 1" using iL by (simp add: mod_if)
    then show ?thesis using False iL by simp
  qed
  then show ?thesis using pm lj xi by (simp add: next_in_def L_def)
qed

lemma lindex_map_inj:
  "inj_on f (set p) \<Longrightarrow> x \<in> set p \<Longrightarrow> lindex (map f p) (f x) = lindex p x"
  by (induction p) (auto simp: inj_on_def)

lemma next_in_map:
  assumes inj: "inj_on f (set p)" and x: "x \<in> set p"
  shows "next_in (map f p) (f x) = f (next_in p x)"
proof -
  have l: "lindex (map f p) (f x) = lindex p x" by (rule lindex_map_inj[OF inj x])
  have "p \<noteq> []" using x by auto
  then have k: "Suc (lindex p x) mod length p < length p" by simp
  have "f x \<in> set (map f p)" using x by simp
  then show ?thesis using x l k by (simp add: next_in_def)
qed

lemma prev_in_map:
  assumes inj: "inj_on f (set p)" and x: "x \<in> set p"
  shows "prev_in (map f p) (f x) = f (prev_in p x)"
proof -
  have l: "lindex (map f p) (f x) = lindex p x" by (rule lindex_map_inj[OF inj x])
  have "p \<noteq> []" using x by auto
  then have k: "(lindex p x + length p - 1) mod length p < length p" by simp
  have "f x \<in> set (map f p)" using x by simp
  then show ?thesis using x l k by (simp add: prev_in_def)
qed

lemma next_in_rev: "distinct p \<Longrightarrow> x \<in> set p \<Longrightarrow> next_in (rev p) x = prev_in p x"
proof -
  assume d: "distinct p" and x: "x \<in> set p"
  define i where "i = lindex p x"
  define L where "L = length p"
  have iL: "i < L" unfolding i_def L_def by (rule lindex_less[OF x])
  have lr: "lindex (rev p) x = L - 1 - i" unfolding i_def L_def by (rule lindex_rev[OF d x])
  have xr: "x \<in> set (rev p)" using x by simp
  have L0: "0 < L" using iL by simp
  have lenr: "length (rev p) = L" by (simp add: L_def)
  have "rev p ! (Suc (L - 1 - i) mod L) = p ! ((i + L - 1) mod L)"
  proof (cases "i = 0")
    case True
    have a: "Suc (L - 1 - i) mod L = 0" using True L0 by simp
    have b: "(i + L - 1) mod L = L - 1" using True L0 by simp
    have "rev p ! 0 = p ! (length p - Suc 0)" using L0 by (simp add: rev_nth L_def)
    then show ?thesis using a b by (simp add: L_def)
  next
    case False
    have a: "Suc (L - 1 - i) mod L = L - i" using False iL by simp
    have b: "(i + L - 1) mod L = i - 1"
    proof -
      have e1: "i + L - 1 = (i - 1) + L" using False by simp
      have e2: "((i - 1) + L) mod L = i - 1" using iL by simp
      show ?thesis unfolding e1 by (rule e2)
    qed
    have c: "L - i < length p" using False iL by (simp add: L_def)
    have "rev p ! (L - i) = p ! (length p - Suc (L - i))" using c by (simp add: rev_nth)
    moreover have "length p - Suc (L - i) = i - 1" using False iL by (simp add: L_def)
    ultimately show ?thesis using a b by simp
  qed
  then show ?thesis using x xr lr by (simp add: next_in_def prev_in_def i_def L_def)
qed

lemma cycle_next_in:
  "cycle (frel g) p \<Longrightarrow> x \<in> set p \<Longrightarrow> g x = next_in p x"
proof -
  assume c: "cycle (frel g) p" and x: "x \<in> set p"
  have "lindex p x < length p" by (rule lindex_less[OF x])
  then have "g (p ! lindex p x) = p ! (Suc (lindex p x) mod length p)"
    using c by (simp add: cycle_nth)
  then show ?thesis using x by (simp add: next_in_def nth_lindex)
qed

section \<open>Counting classes through a map\<close>

lemma card_image_kernel:
  assumes k: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> f x = f y \<longleftrightarrow> g x = g y"
  shows "card (f ` X) = card (g ` X)"
proof -
  define \<phi> where "\<phi> S = g (SOME x. x \<in> X \<and> f x = S)" for S
  have \<phi>f: "\<phi> (f x) = g x" if x: "x \<in> X" for x
  proof -
    have ex: "\<exists>y. y \<in> X \<and> f y = f x" using x by blast
    define y where "y = (SOME y. y \<in> X \<and> f y = f x)"
    have y: "y \<in> X \<and> f y = f x" unfolding y_def by (rule someI_ex[OF ex])
    then have "g y = g x" using k x by blast
    then show ?thesis using y by (simp add: \<phi>_def y_def)
  qed
  have img: "g ` X = \<phi> ` (f ` X)"
  proof
    show "g ` X \<subseteq> \<phi> ` f ` X"
    proof
      fix z assume "z \<in> g ` X"
      then obtain x where x: "x \<in> X" "z = g x" by blast
      then have "z = \<phi> (f x)" using \<phi>f by simp
      then show "z \<in> \<phi> ` f ` X" using x(1) by blast
    qed
    show "\<phi> ` f ` X \<subseteq> g ` X"
    proof
      fix z assume "z \<in> \<phi> ` f ` X"
      then obtain x where x: "x \<in> X" "z = \<phi> (f x)" by blast
      then have "z = g x" using \<phi>f by simp
      then show "z \<in> g ` X" using x(1) by blast
    qed
  qed
  have "inj_on \<phi> (f ` X)"
  proof (rule inj_onI)
    fix S T assume "S \<in> f ` X" "T \<in> f ` X" and eq: "\<phi> S = \<phi> T"
    then obtain x y where xy: "x \<in> X" "y \<in> X" "S = f x" "T = f y" by blast
    then have "g x = g y" using eq \<phi>f by simp
    then show "S = T" using k xy by simp
  qed
  then show ?thesis using img by (simp add: card_image)
qed

lemma card_classes_reflect:
  assumes refl: "\<And>x y. x \<in> A' \<Longrightarrow> y \<in> A' \<Longrightarrow> C' x = C' y \<longleftrightarrow> C (h x) = C (h y)"
    and into: "h ` A' \<subseteq> A" and onto: "\<And>z. z \<in> A \<Longrightarrow> \<exists>x \<in> A'. C (h x) = C z"
  shows "card (C' ` A') = card (C ` A)"
proof -
  have "card (C' ` A') = card ((\<lambda>x. C (h x)) ` A')" by (rule card_image_kernel) (rule refl)
  moreover have "(\<lambda>x. C (h x)) ` A' = C ` A"
  proof
    show "(\<lambda>x. C (h x)) ` A' \<subseteq> C ` A" using into by auto
    show "C ` A \<subseteq> (\<lambda>x. C (h x)) ` A'"
    proof
      fix S assume "S \<in> C ` A"
      then obtain z where z: "z \<in> A" "S = C z" by blast
      obtain x where x: "x \<in> A'" "C (h x) = C z" using onto[OF z(1)] by blast
      have "S = C (h x)" using x(2) z(2) by simp
      then show "S \<in> (\<lambda>x. C (h x)) ` A'" using x(1) by (rule image_eqI)
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma card_classes_split:
  assumes A: "A \<subseteq> S" and fin: "finite S"
    and sep: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> S - A \<Longrightarrow> C x \<noteq> C y"
  shows "card (C ` S) = card (C ` A) + card (C ` (S - A))"
proof -
  have "C ` S = C ` A \<union> C ` (S - A)" using A by blast
  moreover have "C ` A \<inter> C ` (S - A) = {}" using sep by blast
  moreover have "finite (C ` A)" "finite (C ` (S - A))" using fin A by (auto intro: finite_subset)
  ultimately show ?thesis by (simp add: card_Un_disjoint)
qed

lemma fcard_hom:
  assumes g': "fperm g' D'" and g: "fperm g D"
    and AD: "A' \<subseteq> D'" and inj: "inj_on h A'" and cl: "\<And>x. x \<in> A' \<Longrightarrow> g' x \<in> A'"
    and com: "\<And>x. x \<in> A' \<Longrightarrow> h (g' x) = g (h x)" and A: "A = h ` A'"
  shows "fcard g' A' = fcard g A"
proof -
  interpret G': fperm g' D' by (rule g')
  interpret G: fperm g D by (rule g)
  have pw: "(g' ^^ k) x \<in> A' \<and> h ((g' ^^ k) x) = (g ^^ k) (h x)" if "x \<in> A'" for k x
    using that by (induction k) (simp_all add: cl com)
  have conn: "fconnect g' x y \<longleftrightarrow> fconnect g (h x) (h y)" if x: "x \<in> A'" and y: "y \<in> A'" for x y
  proof
    assume "fconnect g' x y"
    then obtain k where "(g' ^^ k) x = y" unfolding fconnect_def by blast
    then show "fconnect g (h x) (h y)" using pw[OF x, of k] unfolding fconnect_def by metis
  next
    assume "fconnect g (h x) (h y)"
    then obtain k where k: "(g ^^ k) (h x) = h y" unfolding fconnect_def by blast
    then have "h ((g' ^^ k) x) = h y" using pw[OF x, of k] by simp
    then have "(g' ^^ k) x = y" using inj_onD[OF inj] pw[OF x, of k] y by blast
    then show "fconnect g' x y" unfolding fconnect_def by blast
  qed
  show ?thesis unfolding fcard_def
  proof (rule card_classes_reflect[where h = h])
    show "\<And>x y. x \<in> A' \<Longrightarrow> y \<in> A' \<Longrightarrow> cyc g' x = cyc g' y \<longleftrightarrow> cyc g (h x) = cyc g (h y)"
      using conn by (simp add: G'.cyc_eq_iff G.cyc_eq_iff)
    show "h ` A' \<subseteq> A" using A by simp
    show "\<And>z. z \<in> A \<Longrightarrow> \<exists>x \<in> A'. cyc g (h x) = cyc g z" using A by blast
  qed
qed

lemma (in fperm) fcard_split_closed:
  assumes A: "A \<subseteq> S" "S \<subseteq> D" and cl: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> A"
  shows "fcard f S = fcard f A + fcard f (S - A)"
proof -
  have cyA: "cyc f x \<subseteq> A" if "x \<in> A" for x
  proof
    fix y assume "y \<in> cyc f x"
    then have "fconnect f x y" by (simp add: in_cyc_iff)
    then show "y \<in> A" by (induction rule: fconnect_induct) (use that cl in auto)
  qed
  show ?thesis unfolding fcard_def
  proof (rule card_classes_split)
    show "finite S" using A(2) fin by (rule finite_subset)
    show "\<And>x y. x \<in> A \<Longrightarrow> y \<in> S - A \<Longrightarrow> cyc f x \<noteq> cyc f y"
      using cyA x_in_cyc by blast
  qed (use A in auto)
qed

lemma (in fperm) fcard_split_cycle:
  assumes c: "cycle (frel f) p" and d: "distinct p" and pS: "set p \<subseteq> S" and S: "S \<subseteq> D"
  shows "fcard f S = (if p = [] then 0 else 1) + fcard f (S - set p)"
proof -
  have cl: "f x \<in> set p" if "x \<in> set p" for x
    using fcycle_fconnect[OF c d that] fconnect_step by blast
  have "fcard f S = fcard f (set p) + fcard f (S - set p)" by (rule fcard_split_closed[OF pS S cl])
  moreover have "fcard f (set p) = (if p = [] then 0 else 1)"
  proof (cases "p = []")
    case False
    have all: "\<forall>x \<in> set p. cyc f x = set p"
      using distinct_cycle_cyc[OF fperm_axioms c d] by blast
    obtain x0 where x0: "x0 \<in> set p" using False by (cases p) auto
    have sub: "cyc f ` set p \<subseteq> {set p}" using all by auto
    have "set p \<in> cyc f ` set p" using all x0 by (metis image_eqI)
    then have "cyc f ` set p = {set p}" using sub by blast
    then show ?thesis using False by (simp add: fcard_def)
  qed (simp add: fcard_def)
  ultimately show ?thesis by simp
qed

locale patch =
  G: hypermap G + Gd: hypermap Gd + Gr: hypermap Gr
  for G :: "'a hypermap" and Gd :: "'b hypermap" and Gr :: "'c hypermap"
  and hd :: "'b \<Rightarrow> 'a" and hr :: "'c \<Rightarrow> 'a" and bGd :: "'b list" and bGr :: "'c list" +
  assumes injd: "inj_on hd (darts Gd)"
    and injr: "inj_on hr (darts Gr)"
    and cycle_d: "cycle (frel (edge Gd)) bGd" and simple_d: "simple Gd bGd"
    and bGd_D: "set bGd \<subseteq> darts Gd"
    and cycle_r: "cycle (frel (node Gr)) bGr" and distinct_r: "distinct bGr"
    and bGr_D: "set bGr \<subseteq> darts Gr"
    and map_ring_r: "map hr bGr = rev (map hd bGd)"
    and codom_d: "hd ` darts Gd \<subseteq> darts G"
    and codom_r: "hr ` darts Gr = (darts G - hd ` darts Gd) \<union> set (map hd bGd)"
    and edge_d: "\<And>x. x \<in> darts Gd \<Longrightarrow> x \<notin> set bGd \<Longrightarrow> hd (edge Gd x) = edge G (hd x)"
    and node_d: "\<And>x. x \<in> darts Gd \<Longrightarrow> hd (node Gd x) = node G (hd x)"
    and edge_r: "\<And>x. x \<in> darts Gr \<Longrightarrow> hr (edge Gr x) = edge G (hr x)"
    and node_r: "\<And>x. x \<in> darts Gr \<Longrightarrow> x \<notin> set bGr \<Longrightarrow> hr (node Gr x) = node G (hr x)"
begin

abbreviation "bG \<equiv> map hd bGd"

lemma distinct_d: "distinct bGd"
  using simple_d Gd.simple_distinct by blast

lemma distinct_bG: "distinct bG"
  using distinct_d injd bGd_D by (simp add: distinct_map inj_on_subset)

lemma set_bG_r: "set (map hr bGr) = set bG"
  using map_ring_r by simp

lemma hd_in_r: "x \<in> darts Gd \<Longrightarrow> hd x \<in> hr ` darts Gr \<longleftrightarrow> x \<in> set bGd"
proof -
  assume xD: "x \<in> darts Gd"
  have "hd x \<in> hr ` darts Gr \<longleftrightarrow> hd x \<in> set bG"
    using codom_r xD by auto
  also have "\<dots> \<longleftrightarrow> x \<in> set bGd"
    using injd xD bGd_D by (auto simp: inj_on_def)
  finally show ?thesis .
qed

lemma codom_d_alt: "hd ` darts Gd = (darts G - hr ` darts Gr) \<union> set bG"
proof -
  have "set bG \<subseteq> hd ` darts Gd" using bGd_D by auto
  moreover have "hr ` darts Gr \<subseteq> darts G" using codom_r codom_d bGd_D by auto
  ultimately show ?thesis using codom_r codom_d by blast
qed

lemma hr_in_d: "x \<in> darts Gr \<Longrightarrow> hr x \<in> hd ` darts Gd \<longleftrightarrow> x \<in> set bGr"
proof -
  assume xD: "x \<in> darts Gr"
  have "hr x \<in> hd ` darts Gd \<longleftrightarrow> hr x \<in> set bG"
    using codom_d_alt xD by auto
  also have "\<dots> \<longleftrightarrow> hr x \<in> set (map hr bGr)" using set_bG_r by simp
  also have "\<dots> \<longleftrightarrow> x \<in> set bGr"
    using injr xD bGr_D by (auto simp: inj_on_def)
  finally show ?thesis .
qed

lemma codom_union: "hd ` darts Gd \<union> hr ` darts Gr = darts G"
  using codom_r codom_d bGd_D by auto

lemma codom_inter: "hd ` darts Gd \<inter> hr ` darts Gr = set bG"
  using codom_r bGd_D by auto

lemma card_patch: "card (darts Gd) + card (darts Gr) = length bG + card (darts G)"
proof -
  have "card (hd ` darts Gd) = card (darts Gd)" using injd by (rule card_image)
  moreover have "card (hr ` darts Gr) = card (darts Gr)" using injr by (rule card_image)
  moreover have "card (hd ` darts Gd \<union> hr ` darts Gr) + card (hd ` darts Gd \<inter> hr ` darts Gr)
      = card (hd ` darts Gd) + card (hr ` darts Gr)"
    using card_Un_Int[of "hd ` darts Gd" "hr ` darts Gr"] Gd.finite_darts Gr.finite_darts by simp
  moreover have "card (set bG) = length bG" using distinct_bG by (rule distinct_card)
  ultimately show ?thesis using codom_union codom_inter by simp
qed

lemma bGd_cycle_cedge: "x \<in> set bGd \<Longrightarrow> fconnect (edge Gd) x y \<longleftrightarrow> y \<in> set bGd"
  using Gd.E.fcycle_fconnect[OF cycle_d distinct_d] by blast

lemma bGr_cycle_cnode: "x \<in> set bGr \<Longrightarrow> fconnect (node Gr) x y \<longleftrightarrow> y \<in> set bGr"
  using Gr.N.fcycle_fconnect[OF cycle_r distinct_r] by blast

lemma bGd_edge: "x \<in> set bGd \<Longrightarrow> edge Gd x \<in> set bGd"
  using bGd_cycle_cedge fconnect_step by blast

lemma bGd_edge_iff: "edge Gd x \<in> set bGd \<longleftrightarrow> x \<in> set bGd"
proof
  assume "edge Gd x \<in> set bGd"
  then have "fconnect (edge Gd) (edge Gd x) x"
    using Gd.E.fconnect_sym fconnect_step by blast
  then show "x \<in> set bGd" using bGd_cycle_cedge \<open>edge Gd x \<in> set bGd\<close> by blast
qed (rule bGd_edge)

lemma bGr_node: "x \<in> set bGr \<Longrightarrow> node Gr x \<in> set bGr"
  using bGr_cycle_cnode fconnect_step by blast

lemma bGr_node_iff: "node Gr x \<in> set bGr \<longleftrightarrow> x \<in> set bGr"
proof
  assume "node Gr x \<in> set bGr"
  then have "fconnect (node Gr) (node Gr x) x"
    using Gr.N.fconnect_sym fconnect_step by blast
  then show "x \<in> set bGr" using bGr_cycle_cnode \<open>node Gr x \<in> set bGr\<close> by blast
qed (rule bGr_node)

lemma hr_in_ring: "x \<in> darts Gr \<Longrightarrow> hr x \<in> set (map hr bGr) \<longleftrightarrow> x \<in> set bGr"
proof
  assume xD: "x \<in> darts Gr" and "hr x \<in> set (map hr bGr)"
  then obtain y where y: "y \<in> set bGr" "hr y = hr x" by auto
  have "y \<in> darts Gr" using y(1) bGr_D by blast
  then have "y = x" using inj_onD[OF injr y(2)] xD by simp
  then show "x \<in> set bGr" using y(1) by simp
qed simp

lemma hdErN:
  assumes xd: "xd \<in> darts Gd" and xr: "xr \<in> darts Gr"
  shows "hd (edge Gd xd) = hr xr \<longleftrightarrow> hd xd = hr (node Gr xr)"
proof (cases "xd \<in> set bGd")
  case False
  have "edge Gd xd \<notin> set bGd" using False bGd_edge_iff by simp
  then have "hd (edge Gd xd) \<notin> hr ` darts Gr" using hd_in_r[of "edge Gd xd"] xd by simp
  moreover have "hd xd \<notin> hr ` darts Gr" using hd_in_r[OF xd] False by simp
  ultimately show ?thesis using xr by auto
next
  case True
  have injbd: "inj_on hd (set bGd)" using injd bGd_D by (rule inj_on_subset)
  have injbr: "inj_on hr (set bGr)" using injr bGr_D by (rule inj_on_subset)
  have e: "edge Gd xd = next_in bGd xd" by (rule cycle_next_in[OF cycle_d True])
  have "hd (edge Gd xd) = next_in bG (hd xd)" using e next_in_map[OF injbd True] by simp
  also have "\<dots> = prev_in (rev bG) (hd xd)"
    using next_in_rev[of "rev bG" "hd xd"] distinct_bG True by simp
  also have "rev bG = map hr bGr" using map_ring_r by simp
  finally have lhs: "hd (edge Gd xd) = prev_in (map hr bGr) (hd xd)" .
  have hxd: "hd xd \<in> set (map hr bGr)" using True set_bG_r by simp
  have dmr: "distinct (map hr bGr)" using distinct_bG map_ring_r by (metis distinct_rev)
  show ?thesis
  proof (cases "xr \<in> set bGr")
    case xrb: True
    have n: "node Gr xr = next_in bGr xr" by (rule cycle_next_in[OF cycle_r xrb])
    have hn: "hr (node Gr xr) = next_in (map hr bGr) (hr xr)"
      using n next_in_map[OF injbr xrb] by simp
    have hxr: "hr xr \<in> set (map hr bGr)" using xrb by simp
    show ?thesis
    proof
      assume "hd (edge Gd xd) = hr xr"
      then have "prev_in (map hr bGr) (hd xd) = hr xr" using lhs by simp
      then have "next_in (map hr bGr) (hr xr) = hd xd" using next_prev_in[OF dmr hxd] by metis
      then show "hd xd = hr (node Gr xr)" using hn by simp
    next
      assume "hd xd = hr (node Gr xr)"
      then have "hd xd = next_in (map hr bGr) (hr xr)" using hn by simp
      then have "prev_in (map hr bGr) (hd xd) = hr xr" using prev_next_in[OF dmr hxr] by simp
      then show "hd (edge Gd xd) = hr xr" using lhs by simp
    qed
  next
    case xrb: False
    have "hd (edge Gd xd) \<in> set (map hr bGr)" using lhs prev_in_mem[OF hxd] by simp
    moreover have "hr xr \<notin> set (map hr bGr)" using hr_in_ring[OF xr] xrb by simp
    ultimately have "hd (edge Gd xd) \<noteq> hr xr" by metis
    moreover have "node Gr xr \<notin> set bGr" using xrb bGr_node_iff by simp
    then have "hr (node Gr xr) \<notin> set (map hr bGr)" using hr_in_ring[of "node Gr xr"] xr by simp
    then have "hd xd \<noteq> hr (node Gr xr)" using hxd by auto
    ultimately show ?thesis by simp
  qed
qed

lemma hdF:
  assumes xd: "xd \<in> darts Gd" "xd \<notin> set bGd"
  shows "hd (face Gd xd) = face G (hd xd)"
proof -
  have fxd: "face Gd xd \<in> darts Gd" using xd by simp
  have nf: "node Gd (face Gd xd) \<notin> set bGd"
  proof
    assume "node Gd (face Gd xd) \<in> set bGd"
    then have "edge Gd (node Gd (face Gd xd)) \<in> set bGd" by (rule bGd_edge)
    then show False using xd Gd.faceK by simp
  qed
  have "hd (edge Gd (node Gd (face Gd xd))) = edge G (hd (node Gd (face Gd xd)))"
    using edge_d nf fxd by simp
  then have "hd xd = edge G (node G (hd (face Gd xd)))" using node_d[OF fxd] Gd.faceK by simp
  then show ?thesis using G.face_eq_iff[of "hd xd" "hd (face Gd xd)"] by simp
qed

lemma hrF:
  assumes xr: "xr \<in> darts Gr" "face Gr xr \<notin> set bGr"
  shows "hr (face Gr xr) = face G (hr xr)"
proof -
  have fxr: "face Gr xr \<in> darts Gr" using xr by simp
  have "hr (node Gr (face Gr xr)) = node G (hr (face Gr xr))" using node_r[OF fxr xr(2)] .
  moreover have "hr (edge Gr (node Gr (face Gr xr))) = edge G (hr (node Gr (face Gr xr)))"
    using edge_r fxr by simp
  ultimately have "hr xr = edge G (node G (hr (face Gr xr)))" using Gr.faceK by simp
  then show ?thesis using G.face_eq_iff[of "hr xr" "hr (face Gr xr)"] by simp
qed

lemma bGdP:
  assumes xd: "xd \<in> set bGd"
  obtains xr where "xr \<in> darts Gr" "hd (edge Gd xd) = hr xr" "hd xd = hr (node Gr xr)"
proof -
  have xdD: "xd \<in> darts Gd" using xd bGd_D by blast
  have "hd xd \<in> hr ` darts Gr" using hd_in_r[OF xdD] xd by simp
  then obtain w where w: "w \<in> darts Gr" "hd xd = hr w" by blast
  define xr where "xr = face Gr (edge Gr w)"
  have xrD: "xr \<in> darts Gr" using w by (simp add: xr_def)
  have nxr: "node Gr xr = w" unfolding xr_def by (rule Gr.edgeK)
  have "hd (edge Gd xd) = hr xr" using hdErN[OF xdD xrD] w nxr by simp
  then show ?thesis using that xrD w nxr by simp
qed

lemma bGrP:
  assumes xr: "xr \<in> set bGr"
  obtains xd where "xd \<in> darts Gd" "hd (edge Gd xd) = hr xr" "hd xd = hr (node Gr xr)"
proof -
  have xrD: "xr \<in> darts Gr" using xr bGr_D by blast
  have "hr xr \<in> hd ` darts Gd" using hr_in_d[OF xrD] xr by simp
  then obtain w where w: "w \<in> darts Gd" "hr xr = hd w" by blast
  define xd where "xd = node Gd (face Gd w)"
  have xdD: "xd \<in> darts Gd" using w by (simp add: xd_def)
  have exd: "edge Gd xd = w" unfolding xd_def by (rule Gd.faceK)
  have "hd xd = hr (node Gr xr)" using hdErN[OF xdD xrD] w exd by simp
  then show ?thesis using that xdD w exd by simp
qed

lemma hd_bGd_iff: "xd \<in> darts Gd \<Longrightarrow> hd xd \<in> set bG \<longleftrightarrow> xd \<in> set bGd"
proof
  assume xD: "xd \<in> darts Gd" and "hd xd \<in> set bG"
  then obtain y where y: "y \<in> set bGd" "hd y = hd xd" by auto
  have "y \<in> darts Gd" using y(1) bGd_D by blast
  then have "y = xd" using inj_onD[OF injd y(2)] xD by simp
  then show "xd \<in> set bGd" using y(1) by simp
qed simp

lemma cFhd:
  assumes xd: "xd \<in> darts Gd"
  shows "G.cface (hd xd) (hd (face Gd xd))"
proof (cases "xd \<in> set bGd")
  case False
  then show ?thesis using hdF[OF xd False] fconnect_step by metis
next
  case xb: True
  have walk: "G.cface (hd y) (hd xd)" if "(face Gd ^^ k) y = xd" "y \<in> darts Gd" for k y
    using that
  proof (induction k arbitrary: y)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    show ?case
    proof (cases "y \<in> set bGd")
      case True
      have "Gd.cface y xd" using Suc.prems(1) fconnect_funpow by metis
      then have "y = xd" using Gd.simple_cface[OF simple_d True xb] by simp
      then show ?thesis by simp
    next
      case False
      have fy: "face Gd y \<in> darts Gd" using Suc.prems(2) by simp
      have "(face Gd ^^ k) (face Gd y) = xd" using Suc.prems(1) by (simp add: funpow_swap1)
      then have ih: "G.cface (hd (face Gd y)) (hd xd)" using Suc.IH fy by blast
      have "hd (face Gd y) = face G (hd y)" using hdF[OF Suc.prems(2) False] .
      then have "G.cface (hd y) (hd (face Gd y))" using fconnect_step by metis
      then show ?thesis by (rule fconnect_trans[OF _ ih])
    qed
  qed
  have o: "Suc (order (face Gd) xd - 1) = order (face Gd) xd" by simp
  have "(face Gd ^^ (order (face Gd) xd - 1)) (face Gd xd) = xd"
    using Gd.F.funpow_order[of xd] o by (metis funpow_simps_right(2) o_apply)
  then have "G.cface (hd (face Gd xd)) (hd xd)" using walk xd by simp
  then show ?thesis by (rule G.F.fconnect_sym)
qed

lemma patch_face_d':
  assumes xd: "xd \<in> darts Gd" and c: "Gd.cface xd yd"
  shows "G.cface (hd xd) (hd yd)"
  using c
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  have "z \<in> darts Gd" using step(1) xd Gd.F.fconnect_in_D by blast
  then have "G.cface (hd z) (hd (face Gd z))" by (rule cFhd)
  then show ?case by (rule fconnect_trans[OF step(2)])
qed

definition outer :: "'a set" where
  "outer = {x \<in> darts G. \<exists>y \<in> hr ` darts Gr. G.cface x y}"

lemma outer_cface:
  assumes xy: "G.cface x y"
  shows "x \<in> outer \<longleftrightarrow> y \<in> outer"
proof -
  have yx: "G.cface y x" by (rule G.F.fconnect_sym[OF xy])
  have D: "x \<in> darts G \<longleftrightarrow> y \<in> darts G" by (rule G.F.fconnect_in_D[OF xy])
  have "(\<exists>w \<in> hr ` darts Gr. G.cface x w) \<longleftrightarrow> (\<exists>w \<in> hr ` darts Gr. G.cface y w)"
    using fconnect_trans[OF xy] fconnect_trans[OF yx] by blast
  then show ?thesis using D by (simp add: outer_def)
qed

lemma hd_notin_outer:
  assumes xd: "xd \<in> darts Gd" and no: "hd xd \<notin> outer"
  shows "xd \<notin> set bGd"
proof
  assume "xd \<in> set bGd"
  then have "hd xd \<in> hr ` darts Gr" using hd_in_r xd by simp
  moreover have "hd xd \<in> darts G" using codom_d xd by blast
  ultimately show False using no by (auto simp: outer_def)
qed

lemma patch_face_d:
  assumes xd: "xd \<in> darts Gd" and yd: "yd \<in> darts Gd" and no: "hd xd \<notin> outer"
  shows "Gd.cface xd yd \<longleftrightarrow> G.cface (hd xd) (hd yd)"
proof
  assume "Gd.cface xd yd"
  then show "G.cface (hd xd) (hd yd)" by (rule patch_face_d'[OF xd])
next
  assume c: "G.cface (hd xd) (hd yd)"
  have lift: "\<exists>w \<in> darts Gd. (face G ^^ k) (hd xd) = hd w \<and> Gd.cface xd w" for k
  proof (induction k)
    case 0
    then show ?case using xd by auto
  next
    case (Suc k)
    then obtain w where w: "w \<in> darts Gd" "(face G ^^ k) (hd xd) = hd w" "Gd.cface xd w" by blast
    have "G.cface (hd xd) (hd w)" using w(2) fconnect_funpow by metis
    then have "hd w \<notin> outer" using no outer_cface by blast
    then have wb: "w \<notin> set bGd" by (rule hd_notin_outer[OF w(1)])
    have "(face G ^^ Suc k) (hd xd) = hd (face Gd w)" using w(2) hdF[OF w(1) wb] by simp
    moreover have "face Gd w \<in> darts Gd" using w(1) by simp
    moreover have "Gd.cface xd (face Gd w)" using w(3) fconnect_stepI_r by metis
    ultimately show ?case by blast
  qed
  obtain k where "(face G ^^ k) (hd xd) = hd yd" using c unfolding fconnect_def by blast
  then obtain w where w: "w \<in> darts Gd" "hd yd = hd w" "Gd.cface xd w" using lift by metis
  have "yd = w" using inj_onD[OF injd w(2) yd w(1)] .
  then show "Gd.cface xd yd" using w(3) by simp
qed

lemma patch_face_r_fwd:
  assumes xr: "xr \<in> darts Gr" and c: "Gr.cface xr yr"
  shows "G.cface (hr xr) (hr yr)"
  using c
proof (induction rule: fconnect_induct)
  case refl
  then show ?case by simp
next
  case (step z)
  have zD: "z \<in> darts Gr" using step(1) xr Gr.F.fconnect_in_D by blast
  have "G.cface (hr z) (hr (face Gr z))"
  proof (cases "face Gr z \<in> set bGr")
    case False
    then show ?thesis using hrF[OF zD False] fconnect_step by metis
  next
    case True
    obtain xd where xd: "xd \<in> darts Gd" "hd (edge Gd xd) = hr (face Gr z)"
      "hd xd = hr (node Gr (face Gr z))" using bGrP[OF True] by blast
    have "hr z = hr (edge Gr (node Gr (face Gr z)))" by (simp add: Gr.faceK)
    also have "\<dots> = edge G (hd xd)" using edge_r[of "node Gr (face Gr z)"] zD xd(3) by simp
    finally have hz: "hr z = edge G (hd xd)" .
    have exd: "edge Gd xd \<in> darts Gd" using xd(1) by simp
    have "hd xd = hd (node Gd (face Gd (edge Gd xd)))" by (simp add: Gd.edgeK)
    also have "\<dots> = node G (hd (face Gd (edge Gd xd)))" using node_d exd by simp
    finally have "edge G (hd xd) = edge G (node G (hd (face Gd (edge Gd xd))))" by simp
    then have "face G (edge G (hd xd)) = hd (face Gd (edge Gd xd))" by (simp add: G.nodeK)
    then have a: "G.cface (edge G (hd xd)) (hd (face Gd (edge Gd xd)))" using fconnect_step by metis
    have "Gd.cface (face Gd (edge Gd xd)) (edge Gd xd)"
      using Gd.F.fconnect_sym fconnect_step by metis
    moreover have "face Gd (edge Gd xd) \<in> darts Gd" using exd by simp
    ultimately have b: "G.cface (hd (face Gd (edge Gd xd))) (hd (edge Gd xd))"
      using patch_face_d' by blast
    have "G.cface (edge G (hd xd)) (hd (edge Gd xd))" by (rule fconnect_trans[OF a b])
    then show ?thesis using hz xd(2) by simp
  qed
  then show ?case by (rule fconnect_trans[OF step(2)])
qed

lemma hr_edge_node_face:
  assumes zD: "z \<in> darts Gr"
  shows "hr (node Gr (face Gr z)) = node G (face G (hr z))"
proof -
  have "edge G (hr (node Gr (face Gr z))) = hr (edge Gr (node Gr (face Gr z)))"
    using edge_r[of "node Gr (face Gr z)"] zD by simp
  also have "\<dots> = hr z" by (simp add: Gr.faceK)
  finally show ?thesis by (simp add: G.edge_eq_iff)
qed

lemma patch_face_r_bwd:
  assumes xr: "xr \<in> darts Gr" and yr: "yr \<in> darts Gr" and c: "G.cface (hr xr) (hr yr)"
  shows "Gr.cface xr yr"
proof -
  define inv where "inv x xr' \<longleftrightarrow> xr' \<in> darts Gr \<and> Gr.cface xr xr' \<and>
     (if x \<in> hr ` darts Gr then x = hr xr'
      else (\<exists>xd \<in> darts Gd. x = hd xd \<and> (\<exists>yd \<in> darts Gd. hd yd = hr xr' \<and> Gd.cface yd xd)))"
    for x xr'
  have step: "\<exists>xr''. inv (face G x) xr''" if I: "inv x xr'" and xG: "x \<in> darts G" for x xr'
  proof -
    have xr'D: "xr' \<in> darts Gr" and cxr': "Gr.cface xr xr'" using I by (auto simp: inv_def)
    have fxr'D: "face Gr xr' \<in> darts Gr" using xr'D by simp
    have cfxr': "Gr.cface xr (face Gr xr')" using cxr' fconnect_stepI_r by metis
    show ?thesis
    proof (cases "x \<in> hr ` darts Gr")
      case xin: True
      then have x: "x = hr xr'" using I by (simp add: inv_def)
      show ?thesis
      proof (cases "face G x \<in> hr ` darts Gr")
        case True
        have "face G x = hr (face Gr xr')"
        proof (cases "face Gr xr' \<in> set bGr")
          case False
          then show ?thesis using hrF[OF xr'D False] x by simp
        next
          case fb: True
          obtain xd where xd: "xd \<in> darts Gd" "hd (edge Gd xd) = hr (face Gr xr')"
            "hd xd = hr (node Gr (face Gr xr'))" using bGrP[OF fb] by blast
          have exd: "edge Gd xd \<in> darts Gd" using xd(1) by simp
          have hx: "x = edge G (hd xd)"
            using x xd(3) hr_edge_node_face[OF xr'D] by (simp add: G.edge_eq_iff G.faceK)
          have "hd xd = node G (hd (face Gd (edge Gd xd)))"
            using node_d[of "face Gd (edge Gd xd)"] exd by (simp add: Gd.edgeK)
          then have fx: "face G x = hd (face Gd (edge Gd xd))" using hx by (simp add: G.nodeK)
          have fexD: "face Gd (edge Gd xd) \<in> darts Gd" using exd by simp
          have "face G x \<in> hd ` darts Gd" using fx fexD by blast
          then have "face G x \<in> hd ` darts Gd \<inter> hr ` darts Gr" using True by blast
          then have "face G x \<in> set bG" using codom_inter by simp
          then have fexb: "face Gd (edge Gd xd) \<in> set bGd" using fx hd_bGd_iff fexD by simp
          have xb: "xd \<in> set bGd"
            using xd(3) hd_in_r[OF xd(1)] xr'D by simp
          then have exb: "edge Gd xd \<in> set bGd" by (rule bGd_edge)
          have "Gd.cface (edge Gd xd) (face Gd (edge Gd xd))" using fconnect_step by metis
          then have "edge Gd xd = face Gd (edge Gd xd)" using Gd.simple_cface[OF simple_d exb fexb] by simp
          then show ?thesis using fx xd(2) by simp
        qed
        then have "inv (face G x) (face Gr xr')" using True fxr'D cfxr' by (simp add: inv_def)
        then show ?thesis by blast
      next
        case False
        have fxG: "face G x \<in> darts G" using xG by simp
        then have "face G x \<in> hd ` darts Gd" using False codom_union by blast
        then obtain xd where xd: "xd \<in> darts Gd" "face G x = hd xd" by blast
        have xb: "xd \<notin> set bGd" using False xd hd_in_r by simp
        define yd where "yd = edge Gd (node Gd xd)"
        have ydD: "yd \<in> darts Gd" using xd(1) by (simp add: yd_def)
        have cyd: "Gd.cface yd xd"
        proof -
          have "face Gd yd = xd" unfolding yd_def by (rule Gd.nodeK)
          then show ?thesis using fconnect_step by metis
        qed
        have ndD: "node Gd xd \<in> darts Gd" using xd(1) by simp
        have "hd (node Gd xd) = node G (face G x)" using node_d[OF xd(1)] xd(2) by simp
        also have "\<dots> = hr (node Gr (face Gr xr'))" using hr_edge_node_face[OF xr'D] x by simp
        finally have "hd yd = hr (face Gr xr')"
          using hdErN[OF ndD fxr'D] by (simp add: yd_def)
        then have ex: "\<exists>xd' \<in> darts Gd. face G x = hd xd' \<and>
                    (\<exists>yd' \<in> darts Gd. hd yd' = hr (face Gr xr') \<and> Gd.cface yd' xd')"
          using xd ydD cyd by blast
        have "inv (face G x) (face Gr xr')" using False fxr'D cfxr' ex by (simp only: inv_def if_False)
        then show ?thesis by blast
      qed
    next
      case xout: False
      then obtain xd yd where xd: "xd \<in> darts Gd" "x = hd xd" and yd: "yd \<in> darts Gd"
        "hd yd = hr xr'" "Gd.cface yd xd" using I by (auto simp: inv_def)
      have xb: "xd \<notin> set bGd" using xout xd hd_in_r by simp
      have fx: "face G x = hd (face Gd xd)" using hdF[OF xd(1) xb] xd(2) by simp
      have fxdD: "face Gd xd \<in> darts Gd" using xd(1) by simp
      have cyf: "Gd.cface yd (face Gd xd)" using yd(3) fconnect_stepI_r by metis
      show ?thesis
      proof (cases "face G x \<in> hr ` darts Gr")
        case True
        have fb: "face Gd xd \<in> set bGd" using True fx hd_in_r[OF fxdD] by simp
        have yb: "yd \<in> set bGd" using yd(2) hd_in_r[OF yd(1)] xr'D by auto
        have "yd = face Gd xd" using Gd.simple_cface[OF simple_d yb fb cyf] .
        then have "face G x = hr xr'" using fx yd(2) by simp
        then have "inv (face G x) xr'" using True xr'D cxr' by (simp add: inv_def)
        then show ?thesis by blast
      next
        case False
        have ex: "\<exists>xd' \<in> darts Gd. face G x = hd xd' \<and>
                    (\<exists>yd' \<in> darts Gd. hd yd' = hr xr' \<and> Gd.cface yd' xd')"
          using fxdD fx yd(1,2) cyf by blast
        have "inv (face G x) xr'" using False xr'D cxr' ex by (simp only: inv_def if_False)
        then show ?thesis by blast
      qed
    qed
  qed
  have reach: "\<exists>xr'. inv ((face G ^^ k) (hr xr)) xr'" for k
  proof (induction k)
    case 0
    have "inv (hr xr) xr" using xr by (simp add: inv_def)
    then show ?case by auto
  next
    case (Suc k)
    then obtain xr' where I: "inv ((face G ^^ k) (hr xr)) xr'" by blast
    have "hr xr \<in> darts G" using xr codom_union by blast
    then have "(face G ^^ k) (hr xr) \<in> darts G" by simp
    then show ?case using step[OF I] by simp
  qed
  obtain k where k: "(face G ^^ k) (hr xr) = hr yr" using c unfolding fconnect_def by blast
  then obtain xr' where I: "inv (hr yr) xr'" using reach by metis
  then have "hr yr = hr xr'" "xr' \<in> darts Gr" "Gr.cface xr xr'"
    using yr by (auto simp: inv_def)
  then have "yr = xr'" using inj_onD[OF injr _ yr] by metis
  then show ?thesis using I by (simp add: inv_def)
qed

lemma patch_face_r:
  "xr \<in> darts Gr \<Longrightarrow> yr \<in> darts Gr \<Longrightarrow> Gr.cface xr yr \<longleftrightarrow> G.cface (hr xr) (hr yr)"
  using patch_face_r_fwd patch_face_r_bwd by blast

subsection \<open>Plain and cubic patches\<close>

lemma hd_eq: "x \<in> darts Gd \<Longrightarrow> y \<in> darts Gd \<Longrightarrow> hd x = hd y \<longleftrightarrow> x = y"
  using inj_onD[OF injd, of x y] by blast

lemma hr_eq: "x \<in> darts Gr \<Longrightarrow> y \<in> darts Gr \<Longrightarrow> hr x = hr y \<longleftrightarrow> x = y"
  using inj_onD[OF injr, of x y] by blast

lemma dartsG_cases:
  assumes "x \<in> darts G"
  obtains (r) xr where "xr \<in> darts Gr" "x = hr xr"
    | (d) xd where "xd \<in> darts Gd" "xd \<notin> set bGd" "x = hd xd"
proof (cases "x \<in> hr ` darts Gr")
  case True
  then show ?thesis using r by blast
next
  case False
  then have "x \<in> hd ` darts Gd" using assms codom_union by blast
  then obtain xd where xd: "xd \<in> darts Gd" "x = hd xd" by blast
  then have "xd \<notin> set bGd" using False hd_in_r by simp
  then show ?thesis using d xd by blast
qed

lemma plain_patch:
  "plain G \<longleftrightarrow> plainb Gd (darts Gd - set bGd) \<and> plain Gr"
proof
  assume pG: "plain G"
  have "plainb Gd (darts Gd - set bGd)"
    unfolding Gd.plainP
  proof
    fix xd assume xd: "xd \<in> darts Gd - set bGd"
    then have xD: "xd \<in> darts Gd" and xb: "xd \<notin> set bGd" by auto
    have exb: "edge Gd xd \<notin> set bGd" using xb bGd_edge_iff by simp
    have exD: "edge Gd xd \<in> darts Gd" using xD by simp
    have "hd (edge Gd (edge Gd xd)) = edge G (edge G (hd xd))"
      using edge_d[OF exD exb] edge_d[OF xD xb] by simp
    also have "\<dots> = hd xd" using G.plain_eq[OF pG] by simp
    finally have a: "edge Gd (edge Gd xd) = xd" using hd_eq[of "edge Gd (edge Gd xd)" xd] xD by simp
    have "hd (edge Gd xd) \<noteq> hd xd"
      using edge_d[OF xD xb] G.plain_neq[OF pG] codom_d xD by auto
    then have "edge Gd xd \<noteq> xd" by auto
    then show "edge Gd (edge Gd xd) = xd \<and> edge Gd xd \<noteq> xd" using a by simp
  qed
  moreover have "plain Gr"
    unfolding plain_def Gr.plainP
  proof
    fix xr assume xD: "xr \<in> darts Gr"
    have exD: "edge Gr xr \<in> darts Gr" using xD by simp
    have "hr (edge Gr (edge Gr xr)) = edge G (edge G (hr xr))"
      using edge_r[OF exD] edge_r[OF xD] by simp
    also have "\<dots> = hr xr" using G.plain_eq[OF pG] by simp
    finally have a: "edge Gr (edge Gr xr) = xr" using hr_eq[of "edge Gr (edge Gr xr)" xr] xD by simp
    have "hr xr \<in> darts G" using xD codom_union by blast
    then have "hr (edge Gr xr) \<noteq> hr xr" using edge_r[OF xD] G.plain_neq[OF pG] by simp
    then have "edge Gr xr \<noteq> xr" by auto
    then show "edge Gr (edge Gr xr) = xr \<and> edge Gr xr \<noteq> xr" using a by simp
  qed
  ultimately show "plainb Gd (darts Gd - set bGd) \<and> plain Gr" by simp
next
  assume h: "plainb Gd (darts Gd - set bGd) \<and> plain Gr"
  have pd: "\<And>xd. xd \<in> darts Gd - set bGd \<Longrightarrow> edge Gd (edge Gd xd) = xd \<and> edge Gd xd \<noteq> xd"
    using h unfolding Gd.plainP[of "darts Gd - set bGd"] by blast
  have pr: "plain Gr" using h by simp
  show "plain G" unfolding plain_def G.plainP
  proof
    fix x assume xG: "x \<in> darts G"
    then show "edge G (edge G x) = x \<and> edge G x \<noteq> x"
    proof (cases rule: dartsG_cases)
      case (r xr)
      have exD: "edge Gr xr \<in> darts Gr" using r(1) by simp
      have "edge G (edge G x) = hr (edge Gr (edge Gr xr))" using r edge_r exD by simp
      also have "\<dots> = x" using Gr.plain_eq[OF pr] r by simp
      finally have a: "edge G (edge G x) = x" .
      have "edge Gr xr \<noteq> xr" using Gr.plain_neq[OF pr r(1)] .
      then have "hr (edge Gr xr) \<noteq> hr xr" using hr_eq[OF exD r(1)] by simp
      then have "edge G x \<noteq> x" using r edge_r by simp
      then show ?thesis using a by simp
    next
      case (d xd)
      have exb: "edge Gd xd \<notin> set bGd" using d(2) bGd_edge_iff by simp
      have exD: "edge Gd xd \<in> darts Gd" using d(1) by simp
      have pxd: "edge Gd (edge Gd xd) = xd \<and> edge Gd xd \<noteq> xd" using pd d(1,2) by simp
      have "edge G (edge G x) = hd (edge Gd (edge Gd xd))"
        using d edge_d[OF d(1) d(2)] edge_d[OF exD exb] by simp
      then have a: "edge G (edge G x) = x" using pxd d by simp
      have "hd (edge Gd xd) \<noteq> hd xd" using pxd hd_eq[OF exD d(1)] by simp
      then have "edge G x \<noteq> x" using d edge_d[OF d(1) d(2)] by simp
      then show ?thesis using a by simp
    qed
  qed
qed

lemma cubic_patch:
  "cubic G \<longleftrightarrow> cubic Gd \<and> cubicb Gr (darts Gr - set bGr)"
proof
  assume cG: "cubic G"
  have "cubic Gd" unfolding cubic_def Gd.cubicP
  proof
    fix xd assume xD: "xd \<in> darts Gd"
    have hx: "hd xd \<in> darts G" using xD codom_d by blast
    have n1: "node Gd xd \<in> darts Gd" and n2: "node Gd (node Gd xd) \<in> darts Gd" using xD by simp_all
    have "hd (node Gd (node Gd (node Gd xd))) = node G (node G (node G (hd xd)))"
      using node_d xD n1 n2 by simp
    also have "\<dots> = hd xd" using G.cubic_eq[OF cG hx] .
    finally have a: "node Gd (node Gd (node Gd xd)) = xd" using hd_eq xD by simp
    have "hd (node Gd xd) \<noteq> hd xd" using node_d[OF xD] G.cubic_neq[OF cG hx] by simp
    then have "node Gd xd \<noteq> xd" by auto
    then show "node Gd (node Gd (node Gd xd)) = xd \<and> node Gd xd \<noteq> xd" using a by simp
  qed
  moreover have "cubicb Gr (darts Gr - set bGr)" unfolding Gr.cubicP
  proof
    fix xr assume xr: "xr \<in> darts Gr - set bGr"
    then have xD: "xr \<in> darts Gr" and xb: "xr \<notin> set bGr" by auto
    have hx: "hr xr \<in> darts G" using xD codom_union by blast
    have n1: "node Gr xr \<in> darts Gr" "node Gr xr \<notin> set bGr" using xD xb bGr_node_iff by simp_all
    have n2: "node Gr (node Gr xr) \<in> darts Gr" "node Gr (node Gr xr) \<notin> set bGr"
      using n1 bGr_node_iff by simp_all
    have "hr (node Gr (node Gr (node Gr xr))) = node G (node G (node G (hr xr)))"
      using node_r[OF xD xb] node_r[OF n1] node_r[OF n2] by simp
    also have "\<dots> = hr xr" using G.cubic_eq[OF cG hx] .
    finally have a: "node Gr (node Gr (node Gr xr)) = xr" using hr_eq xD by simp
    have "hr (node Gr xr) \<noteq> hr xr" using node_r[OF xD xb] G.cubic_neq[OF cG hx] by simp
    then have "node Gr xr \<noteq> xr" by auto
    then show "node Gr (node Gr (node Gr xr)) = xr \<and> node Gr xr \<noteq> xr" using a by simp
  qed
  ultimately show "cubic Gd \<and> cubicb Gr (darts Gr - set bGr)" by simp
next
  assume h: "cubic Gd \<and> cubicb Gr (darts Gr - set bGr)"
  have cd: "cubic Gd" using h by simp
  have cr: "\<And>xr. xr \<in> darts Gr - set bGr \<Longrightarrow> node Gr (node Gr (node Gr xr)) = xr \<and> node Gr xr \<noteq> xr"
    using h unfolding Gr.cubicP[of "darts Gr - set bGr"] by blast
  show "cubic G" unfolding cubic_def G.cubicP
  proof
    fix x assume xG: "x \<in> darts G"
    show "node G (node G (node G x)) = x \<and> node G x \<noteq> x"
    proof (cases "x \<in> hd ` darts Gd")
      case True
      then obtain xd where xd: "xd \<in> darts Gd" "x = hd xd" by blast
      have n1: "node Gd xd \<in> darts Gd" and n2: "node Gd (node Gd xd) \<in> darts Gd" using xd by simp_all
      have "node G (node G (node G x)) = hd (node Gd (node Gd (node Gd xd)))"
        using node_d xd n1 n2 by simp
      also have "\<dots> = x" using Gd.cubic_eq[OF cd xd(1)] xd by simp
      finally have a: "node G (node G (node G x)) = x" .
      have "hd (node Gd xd) \<noteq> hd xd" using Gd.cubic_neq[OF cd xd(1)] hd_eq[OF n1 xd(1)] by simp
      then have "node G x \<noteq> x" using xd node_d by simp
      then show ?thesis using a by simp
    next
      case False
      then have "x \<in> hr ` darts Gr" using xG codom_union by blast
      then obtain xr where xr: "xr \<in> darts Gr" "x = hr xr" by blast
      have xb: "xr \<notin> set bGr" using False xr hr_in_d by simp
      have n1: "node Gr xr \<in> darts Gr" "node Gr xr \<notin> set bGr" using xr xb bGr_node_iff by simp_all
      have n2: "node Gr (node Gr xr) \<in> darts Gr" "node Gr (node Gr xr) \<notin> set bGr"
        using n1 bGr_node_iff by simp_all
      have cxr: "node Gr (node Gr (node Gr xr)) = xr \<and> node Gr xr \<noteq> xr" using cr xr(1) xb by simp
      have "node G (node G (node G x)) = hr (node Gr (node Gr (node Gr xr)))"
        using xr node_r[OF xr(1) xb] node_r[OF n1] node_r[OF n2] by simp
      then have a: "node G (node G (node G x)) = x" using cxr xr by simp
      have "hr (node Gr xr) \<noteq> hr xr" using cxr hr_eq[OF n1(1) xr(1)] by simp
      then have "node G x \<noteq> x" using xr node_r[OF xr(1) xb] by simp
      then show ?thesis using a by simp
    qed
  qed
qed

subsection \<open>Cycle counts\<close>

lemma codom_hd_off: "hd ` (darts Gd - set bGd) = darts G - hr ` darts Gr"
proof
  show "hd ` (darts Gd - set bGd) \<subseteq> darts G - hr ` darts Gr"
  proof
    fix x assume "x \<in> hd ` (darts Gd - set bGd)"
    then obtain y where y: "y \<in> darts Gd" "y \<notin> set bGd" "x = hd y" by blast
    have "hd y \<notin> hr ` darts Gr" using hd_in_r[OF y(1)] y(2) by simp
    moreover have "hd y \<in> darts G" using codom_d y(1) by blast
    ultimately show "x \<in> darts G - hr ` darts Gr" using y(3) by simp
  qed
  show "darts G - hr ` darts Gr \<subseteq> hd ` (darts Gd - set bGd)"
  proof
    fix x assume x: "x \<in> darts G - hr ` darts Gr"
    then have "x \<in> hd ` darts Gd" using codom_union by blast
    then obtain y where y: "y \<in> darts Gd" "x = hd y" by blast
    then have "y \<notin> set bGd" using x hd_in_r by auto
    then show "x \<in> hd ` (darts Gd - set bGd)" using y by blast
  qed
qed

lemma codom_hr_off: "hr ` (darts Gr - set bGr) = darts G - hd ` darts Gd"
proof
  show "hr ` (darts Gr - set bGr) \<subseteq> darts G - hd ` darts Gd"
  proof
    fix x assume "x \<in> hr ` (darts Gr - set bGr)"
    then obtain y where y: "y \<in> darts Gr" "y \<notin> set bGr" "x = hr y" by blast
    have "hr y \<notin> hd ` darts Gd" using hr_in_d[OF y(1)] y(2) by simp
    moreover have "hr y \<in> darts G" using codom_union y(1) by blast
    ultimately show "x \<in> darts G - hd ` darts Gd" using y(3) by simp
  qed
  show "darts G - hd ` darts Gd \<subseteq> hr ` (darts Gr - set bGr)"
  proof
    fix x assume x: "x \<in> darts G - hd ` darts Gd"
    then have "x \<in> hr ` darts Gr" using codom_union by blast
    then obtain y where y: "y \<in> darts Gr" "x = hr y" by blast
    then have "y \<notin> set bGr" using x hr_in_d by auto
    then show "x \<in> hr ` (darts Gr - set bGr)" using y by blast
  qed
qed

lemma length_bGr: "length bGr = length bGd"
  using arg_cong[OF map_ring_r, of length] by simp

lemma fcard_edge_r: "fcard (edge Gr) (darts Gr) = fcard (edge G) (hr ` darts Gr)"
  by (rule fcard_hom[OF Gr.E.fperm_axioms G.E.fperm_axioms subset_refl injr]) (simp_all add: edge_r)

lemma fcard_edge_d:
  "fcard (edge Gd) (darts Gd) = (if bGd = [] then 0 else 1) + fcard (edge G) (darts G - hr ` darts Gr)"
proof -
  have "fcard (edge Gd) (darts Gd) = (if bGd = [] then 0 else 1) + fcard (edge Gd) (darts Gd - set bGd)"
    by (rule Gd.E.fcard_split_cycle[OF cycle_d distinct_d bGd_D subset_refl])
  moreover have "fcard (edge Gd) (darts Gd - set bGd) = fcard (edge G) (darts G - hr ` darts Gr)"
  proof (rule fcard_hom[OF Gd.E.fperm_axioms G.E.fperm_axioms])
    show "inj_on hd (darts Gd - set bGd)" using injd by (rule inj_on_subset) blast
    show "\<And>x. x \<in> darts Gd - set bGd \<Longrightarrow> edge Gd x \<in> darts Gd - set bGd"
      using bGd_edge_iff by simp
    show "\<And>x. x \<in> darts Gd - set bGd \<Longrightarrow> hd (edge Gd x) = edge G (hd x)" using edge_d by simp
    show "darts G - hr ` darts Gr = hd ` (darts Gd - set bGd)" using codom_hd_off by simp
  qed blast
  ultimately show ?thesis by simp
qed

lemma fcard_node_d: "fcard (node Gd) (darts Gd) = fcard (node G) (hd ` darts Gd)"
  by (rule fcard_hom[OF Gd.N.fperm_axioms G.N.fperm_axioms subset_refl injd]) (simp_all add: node_d)

lemma fcard_node_r:
  "fcard (node Gr) (darts Gr) = (if bGd = [] then 0 else 1) + fcard (node G) (darts G - hd ` darts Gd)"
proof -
  have e: "(bGr = []) = (bGd = [])" using length_bGr by auto
  have "fcard (node Gr) (darts Gr) = (if bGr = [] then 0 else 1) + fcard (node Gr) (darts Gr - set bGr)"
    by (rule Gr.N.fcard_split_cycle[OF cycle_r distinct_r bGr_D subset_refl])
  moreover have "fcard (node Gr) (darts Gr - set bGr) = fcard (node G) (darts G - hd ` darts Gd)"
  proof (rule fcard_hom[OF Gr.N.fperm_axioms G.N.fperm_axioms])
    show "inj_on hr (darts Gr - set bGr)" using injr by (rule inj_on_subset) blast
    show "\<And>x. x \<in> darts Gr - set bGr \<Longrightarrow> node Gr x \<in> darts Gr - set bGr"
      using bGr_node_iff by simp
    show "\<And>x. x \<in> darts Gr - set bGr \<Longrightarrow> hr (node Gr x) = node G (hr x)" using node_r by simp
    show "darts G - hd ` darts Gd = hr ` (darts Gr - set bGr)" using codom_hr_off by simp
  qed blast
  ultimately show ?thesis using e by simp
qed

lemma fcard_face_r: "fcard (face Gr) (darts Gr) = fcard (face G) outer"
  unfolding fcard_def
proof (rule card_classes_reflect[where h = hr])
  show "\<And>x y. x \<in> darts Gr \<Longrightarrow> y \<in> darts Gr \<Longrightarrow>
      cyc (face Gr) x = cyc (face Gr) y \<longleftrightarrow> cyc (face G) (hr x) = cyc (face G) (hr y)"
    using patch_face_r by (simp add: Gr.F.cyc_eq_iff G.F.cyc_eq_iff)
  show "hr ` darts Gr \<subseteq> outer"
    using codom_union by (auto simp: outer_def)
  show "\<And>z. z \<in> outer \<Longrightarrow> \<exists>x \<in> darts Gr. cyc (face G) (hr x) = cyc (face G) z"
    by (auto simp: outer_def G.F.cyc_eq_iff) (metis G.F.fconnect_sym)
qed

lemma outer_hd:
  assumes xd: "xd \<in> darts Gd"
  shows "hd xd \<in> outer \<longleftrightarrow> fband Gd bGd xd"
proof
  assume "fband Gd bGd xd"
  then obtain yd where yd: "yd \<in> set bGd" "Gd.cface xd yd" by (auto simp: fband_def)
  have "G.cface (hd xd) (hd yd)" by (rule patch_face_d'[OF xd yd(2)])
  moreover have "hd yd \<in> hr ` darts Gr" using yd(1) bGd_D hd_in_r by blast
  moreover have "hd xd \<in> darts G" using xd codom_d by blast
  ultimately show "hd xd \<in> outer" by (auto simp: outer_def)
next
  assume out: "hd xd \<in> outer"
  show "fband Gd bGd xd"
  proof (rule ccontr)
    assume nf: "\<not> fband Gd bGd xd"
    have lift: "\<exists>w \<in> darts Gd. (face G ^^ k) (hd xd) = hd w \<and> Gd.cface xd w" for k
    proof (induction k)
      case 0
      then show ?case using xd by auto
    next
      case (Suc k)
      then obtain w where w: "w \<in> darts Gd" "(face G ^^ k) (hd xd) = hd w" "Gd.cface xd w" by blast
      have wb: "w \<notin> set bGd" using nf w(3) by (auto simp: fband_def)
      have "(face G ^^ Suc k) (hd xd) = hd (face Gd w)" using w(2) hdF[OF w(1) wb] by simp
      moreover have "Gd.cface xd (face Gd w)" using w(3) fconnect_stepI_r by metis
      ultimately show ?case using w(1) by auto
    qed
    obtain y where y: "y \<in> hr ` darts Gr" "G.cface (hd xd) y" using out by (auto simp: outer_def)
    then obtain k where "(face G ^^ k) (hd xd) = y" unfolding fconnect_def by blast
    then obtain w where w: "w \<in> darts Gd" "y = hd w" "Gd.cface xd w" using lift by metis
    have "w \<notin> set bGd" using nf w(3) by (auto simp: fband_def)
    then show False using y(1) w hd_in_r by simp
  qed
qed

lemma fcard_face_d:
  "fcard (face Gd) (darts Gd) = length bGd + fcard (face G) (darts G - outer)"
proof -
  define F where "F = {x \<in> darts Gd. fband Gd bGd x}"
  have FD: "F \<subseteq> darts Gd" by (auto simp: F_def)
  have clF: "face Gd x \<in> F" if "x \<in> F" for x using that by (auto simp: F_def)
  have "fcard (face Gd) (darts Gd) = fcard (face Gd) F + fcard (face Gd) (darts Gd - F)"
    by (rule Gd.F.fcard_split_closed[OF FD subset_refl clF])
  moreover have "fcard (face Gd) F = length bGd"
    using Gd.simple_fcard_fband[OF simple_d bGd_D] by (simp add: F_def)
  moreover have "fcard (face Gd) (darts Gd - F) = fcard (face G) (darts G - outer)"
  proof (rule fcard_hom[OF Gd.F.fperm_axioms G.F.fperm_axioms])
    show "inj_on hd (darts Gd - F)" using injd by (rule inj_on_subset) blast
    show "\<And>x. x \<in> darts Gd - F \<Longrightarrow> face Gd x \<in> darts Gd - F" by (auto simp: F_def)
    show "\<And>x. x \<in> darts Gd - F \<Longrightarrow> hd (face Gd x) = face G (hd x)"
      using hdF by (auto simp: F_def fband_def)
    show "darts G - outer = hd ` (darts Gd - F)"
    proof
      show "darts G - outer \<subseteq> hd ` (darts Gd - F)"
      proof
        fix x assume x: "x \<in> darts G - outer"
        then have "x \<notin> hr ` darts Gr" by (auto simp: outer_def)
        then have "x \<in> hd ` darts Gd" using x codom_union by blast
        then obtain y where y: "y \<in> darts Gd" "x = hd y" by blast
        then have "y \<notin> F" using x outer_hd by (simp add: F_def)
        then show "x \<in> hd ` (darts Gd - F)" using y by blast
      qed
      show "hd ` (darts Gd - F) \<subseteq> darts G - outer"
        using outer_hd codom_d by (auto simp: F_def)
    qed
  qed blast
  ultimately show ?thesis by simp
qed

lemma fcard_G_split:
  "fcard (edge G) (darts G) = fcard (edge G) (hr ` darts Gr) + fcard (edge G) (darts G - hr ` darts Gr)"
  "fcard (node G) (darts G) = fcard (node G) (hd ` darts Gd) + fcard (node G) (darts G - hd ` darts Gd)"
  "fcard (face G) (darts G) = fcard (face G) outer + fcard (face G) (darts G - outer)"
proof -
  show "fcard (edge G) (darts G) = fcard (edge G) (hr ` darts Gr) + fcard (edge G) (darts G - hr ` darts Gr)"
  proof (rule G.E.fcard_split_closed)
    show "\<And>x. x \<in> hr ` darts Gr \<Longrightarrow> edge G x \<in> hr ` darts Gr"
    proof -
      fix x assume "x \<in> hr ` darts Gr"
      then obtain y where y: "y \<in> darts Gr" "x = hr y" by blast
      then have "edge G x = hr (edge Gr y)" using edge_r by simp
      then show "edge G x \<in> hr ` darts Gr" using y(1) by simp
    qed
  qed (use codom_union in auto)
  show "fcard (node G) (darts G) = fcard (node G) (hd ` darts Gd) + fcard (node G) (darts G - hd ` darts Gd)"
  proof (rule G.N.fcard_split_closed)
    show "\<And>x. x \<in> hd ` darts Gd \<Longrightarrow> node G x \<in> hd ` darts Gd"
    proof -
      fix x assume "x \<in> hd ` darts Gd"
      then obtain y where y: "y \<in> darts Gd" "x = hd y" by blast
      then have "node G x = hd (node Gd y)" using node_d by simp
      then show "node G x \<in> hd ` darts Gd" using y(1) by simp
    qed
  qed (use codom_union in auto)
  show "fcard (face G) (darts G) = fcard (face G) outer + fcard (face G) (darts G - outer)"
  proof (rule G.F.fcard_split_closed)
    show "\<And>x. x \<in> outer \<Longrightarrow> face G x \<in> outer"
      using outer_cface fconnect_step by blast
  qed (auto simp: outer_def)
qed

subsection \<open>Components\<close>

lemma (in hypermap) comp_eq_iff: "comp_of (glink G) x = comp_of (glink G) y \<longleftrightarrow> gcomp G x y"
proof
  assume eq: "comp_of (glink G) x = comp_of (glink G) y"
  have "y \<in> comp_of (glink G) y" by (simp add: comp_of_def)
  then have "y \<in> comp_of (glink G) x" by (simp only: eq)
  then show "gcomp G x y" by (simp add: comp_of_def)
qed (rule comp_eq)

definition acl :: "'a set" where
  "acl = {x \<in> darts G. \<exists>y \<in> hr ` darts Gr. gcomp G x y}"

lemma glink_hd:
  assumes xd: "xd \<in> darts Gd" "xd \<notin> set bGd" and l: "glink G (hd xd) z"
  shows "\<exists>yd \<in> darts Gd. z = hd yd \<and> glink Gd xd yd"
proof -
  have e: "edge G (hd xd) = hd (edge Gd xd)" using edge_d[OF xd] by simp
  have n: "node G (hd xd) = hd (node Gd xd)" using node_d[OF xd(1)] by simp
  have f: "face G (hd xd) = hd (face Gd xd)" using hdF[OF xd] by simp
  show ?thesis using l e n f xd(1) by (auto simp: glink_def)
qed

lemma glink_hd_rev:
  assumes xd: "xd \<in> darts Gd" "xd \<notin> set bGd" and l: "glink Gd xd yd"
  shows "glink G (hd xd) (hd yd)"
  using l edge_d[OF xd] node_d[OF xd(1)] hdF[OF xd] by (auto simp: glink_def)

lemma glink_r_gcomp:
  assumes xr: "xr \<in> darts Gr" and l: "glink Gr xr yr"
  shows "gcomp G (hr xr) (hr yr)"
proof -
  consider "edge Gr xr = yr" | "node Gr xr = yr" | "face Gr xr = yr" using l by (auto simp: glink_def)
  then show ?thesis
  proof cases
    case 1
    then have "glink G (hr xr) (hr yr)" using edge_r[OF xr] by (simp add: glink_def)
    then show ?thesis by (rule r_into_rtranclp)
  next
    case 2
    define y where "y = node Gr xr"
    have yD: "y \<in> darts Gr" using xr by (simp add: y_def)
    have fey: "face Gr (edge Gr y) = xr" unfolding y_def by (rule Gr.nodeK)
    have "Gr.cface (edge Gr y) xr" using fconnect_step[of "face Gr" "edge Gr y"] fey by simp
    then have c: "G.cface (hr (edge Gr y)) (hr xr)" using patch_face_r yD xr by simp
    have "glink G (hr y) (hr (edge Gr y))" using edge_r[OF yD] by (simp add: glink_def)
    then have "gcomp G (hr y) (hr xr)"
      by (rule converse_rtranclp_into_rtranclp[OF _ G.cface_gcomp[OF c]])
    then show ?thesis using G.gcomp_sym 2 by (simp add: y_def)
  next
    case 3
    have yD: "yr \<in> darts Gr" using 3 xr by auto
    have "Gr.cface xr yr" using 3 fconnect_step by metis
    then have "G.cface (hr xr) (hr yr)" using patch_face_r[OF xr yD] by simp
    then show ?thesis by (rule G.cface_gcomp)
  qed
qed

lemma gcomp_r_gcomp: "xr \<in> darts Gr \<Longrightarrow> gcomp Gr xr yr \<Longrightarrow> gcomp G (hr xr) (hr yr)"
proof -
  assume xr: "xr \<in> darts Gr" and c: "gcomp Gr xr yr"
  show ?thesis using c
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    have "y \<in> darts Gr" using step(1) xr Gr.gcomp_closed by blast
    then show ?case by (rule rtranclp_trans[OF step(3) glink_r_gcomp[OF _ step(2)]])
  qed
qed

lemma border_r_gcomp: "b1 \<in> set bGr \<Longrightarrow> b2 \<in> set bGr \<Longrightarrow> gcomp Gr b1 b2"
  using bGr_cycle_cnode Gr.cnode_gcomp by blast

lemma gcomp_reflect_r:
  assumes xr: "xr \<in> darts Gr" and yr: "yr \<in> darts Gr" and c: "gcomp G (hr xr) (hr yr)"
  shows "gcomp Gr xr yr"
proof -
  define I where "I x ur \<longleftrightarrow> ur \<in> darts Gr \<and> gcomp Gr xr ur \<and>
      (x \<in> hr ` darts Gr \<longrightarrow> x = hr ur) \<and> (x \<notin> hr ` darts Gr \<longrightarrow> ur \<in> set bGr)" for x ur
  have step: "\<exists>ur'. I x' ur'" if Ix: "I x ur" and xG: "x \<in> darts G" and l: "glink G x x'" for x x' ur
  proof -
    have urD: "ur \<in> darts Gr" and cur: "gcomp Gr xr ur" using Ix by (auto simp: I_def)
    have trans: "gcomp Gr xr u" if "gcomp Gr ur u" for u by (rule rtranclp_trans[OF cur that])
    show ?thesis
    proof (cases "x \<in> hr ` darts Gr")
      case xin: True
      then have x: "x = hr ur" using Ix by (simp add: I_def)
      show ?thesis
      proof (cases "x' \<in> hr ` darts Gr")
        case True
        then obtain ur' where ur': "ur' \<in> darts Gr" "x' = hr ur'" by blast
        have "gcomp Gr ur ur'"
        proof -
          consider "edge G x = x'" | "node G x = x'" | "face G x = x'" using l by (auto simp: glink_def)
          then show ?thesis
          proof cases
            case 1
            then have "hr (edge Gr ur) = hr ur'" using x ur' edge_r[OF urD] by simp
            then have "edge Gr ur = ur'" using hr_eq urD ur'(1) by simp
            then show ?thesis using Gr.glinkE r_into_rtranclp by metis
          next
            case 2
            show ?thesis
            proof (cases "ur \<in> set bGr")
              case False
              then have "hr (node Gr ur) = hr ur'" using x ur' 2 node_r[OF urD] by simp
              then have "node Gr ur = ur'" using hr_eq urD ur'(1) by simp
              then show ?thesis using Gr.glinkN r_into_rtranclp by metis
            next
              case True
              have "hr ur \<in> hd ` darts Gd" using hr_in_d[OF urD] True by simp
              then obtain w where w: "w \<in> darts Gd" "hr ur = hd w" by blast
              have "x' = hd (node Gd w)" using 2 x w node_d by simp
              then have "x' \<in> hd ` darts Gd" using w(1) by simp
              then have "ur' \<in> set bGr" using hr_in_d[OF ur'(1)] ur'(2) by simp
              then show ?thesis using border_r_gcomp True by simp
            qed
          next
            case 3
            then have "G.cface (hr ur) (hr ur')" using x ur' fconnect_step by metis
            then have "Gr.cface ur ur'" using patch_face_r urD ur'(1) by simp
            then show ?thesis by (rule Gr.cface_gcomp)
          qed
        qed
        then have "I x' ur'" using True ur' trans by (simp add: I_def)
        then show ?thesis by blast
      next
        case False
        have "\<exists>ur'. ur' \<in> set bGr \<and> gcomp Gr ur ur'"
        proof -
          consider "edge G x = x'" | "node G x = x'" | "face G x = x'" using l by (auto simp: glink_def)
          then show ?thesis
          proof cases
            case 1
            then have "x' = hr (edge Gr ur)" using x edge_r[OF urD] by simp
            then show ?thesis using False urD by simp
          next
            case 2
            have "ur \<in> set bGr"
            proof (rule ccontr)
              assume "ur \<notin> set bGr"
              then have "x' = hr (node Gr ur)" using x 2 node_r[OF urD] by simp
              then show False using False urD by simp
            qed
            then show ?thesis by blast
          next
            case 3
            have fb: "face Gr ur \<in> set bGr"
            proof (rule ccontr)
              assume "face Gr ur \<notin> set bGr"
              then have "x' = hr (face Gr ur)" using x 3 hrF[OF urD] by simp
              then show False using False urD by simp
            qed
            have "gcomp Gr ur (face Gr ur)" using Gr.glinkF r_into_rtranclp by metis
            then show ?thesis using fb by blast
          qed
        qed
        then obtain ur' where ur': "ur' \<in> set bGr" "gcomp Gr ur ur'" by blast
        have "ur' \<in> darts Gr" using ur'(1) bGr_D by blast
        then have "I x' ur'" using False ur' trans by (simp add: I_def)
        then show ?thesis by blast
      qed
    next
      case xout: False
      then have urb: "ur \<in> set bGr" using Ix by (simp add: I_def)
      show ?thesis
      proof (cases "x' \<in> hr ` darts Gr")
        case False
        then have "I x' ur" using urD cur urb by (simp add: I_def)
        then show ?thesis by blast
      next
        case True
        then obtain ur' where ur': "ur' \<in> darts Gr" "x' = hr ur'" by blast
        have "x \<in> hd ` darts Gd" using xG xout codom_union by blast
        then obtain w where w: "w \<in> darts Gd" "x = hd w" by blast
        have wb: "w \<notin> set bGd" using xout w hd_in_r by simp
        obtain w' where w': "w' \<in> darts Gd" "x' = hd w'" using glink_hd[OF w(1) wb] l w(2) by blast
        then have "x' \<in> hd ` darts Gd" by simp
        then have ur'b: "ur' \<in> set bGr" using hr_in_d[OF ur'(1)] ur'(2) by simp
        then have "gcomp Gr ur ur'" using border_r_gcomp urb by simp
        then have "I x' ur'" using True ur' trans by (simp add: I_def)
        then show ?thesis by blast
      qed
    qed
  qed
  obtain P where P: "path (glink G) (hr xr) P" "lastd (hr xr) P = hr yr"
    using c connect_path by metis
  have hxG: "hr xr \<in> darts G" using xr codom_union by blast
  have walk: "\<exists>ur. I (lastd x P') ur" if "path (glink G) x P'" "I x u" "x \<in> darts G" for x u P'
    using that
  proof (induction P' arbitrary: x u)
    case Nil
    then show ?case by auto
  next
    case (Cons z P')
    have l: "glink G x z" and pz: "path (glink G) z P'" using Cons.prems(1) by auto
    obtain u' where u': "I z u'" using step[OF Cons.prems(2) Cons.prems(3) l] by blast
    have "z \<in> darts G" using l Cons.prems(3) G.glink_closed by blast
    then show ?case using Cons.IH[OF pz u'] by simp
  qed
  have "I (hr xr) xr" using xr by (simp add: I_def)
  then obtain ur where "I (hr yr) ur" using walk[OF P(1) _ hxG] P(2) by metis
  then have ur: "ur \<in> darts Gr" "gcomp Gr xr ur" "hr yr = hr ur" using yr by (auto simp: I_def)
  then have "yr = ur" using hr_eq yr by simp
  then show ?thesis using ur(2) by simp
qed

lemma n_comp_r: "n_comp (glink Gr) (darts Gr) = n_comp (glink G) acl"
  unfolding n_comp_def
proof (rule card_classes_reflect[where h = hr])
  show "\<And>x y. x \<in> darts Gr \<Longrightarrow> y \<in> darts Gr \<Longrightarrow>
      comp_of (glink Gr) x = comp_of (glink Gr) y \<longleftrightarrow> comp_of (glink G) (hr x) = comp_of (glink G) (hr y)"
    using gcomp_r_gcomp gcomp_reflect_r by (simp add: Gr.comp_eq_iff G.comp_eq_iff) blast
  show "hr ` darts Gr \<subseteq> acl" using codom_union by (auto simp: acl_def)
  show "\<And>z. z \<in> acl \<Longrightarrow> \<exists>x \<in> darts Gr. comp_of (glink G) (hr x) = comp_of (glink G) z"
    by (auto simp: acl_def G.comp_eq_iff) (metis G.gcomp_sym)
qed

lemma acl_closed:
  assumes "x \<in> acl" "gcomp G x y" shows "y \<in> acl"
proof -
  obtain z where z: "z \<in> hr ` darts Gr" "gcomp G x z" using assms(1) by (auto simp: acl_def)
  have "gcomp G y z" by (rule rtranclp_trans[OF G.gcomp_sym[OF assms(2)] z(2)])
  moreover have "y \<in> darts G" using assms acl_def G.gcomp_closed by blast
  ultimately show ?thesis using z(1) by (auto simp: acl_def)
qed

lemma acl_closed_rev:
  assumes "y \<in> acl" "gcomp G x y" shows "x \<in> acl"
  using acl_closed[OF assms(1) G.gcomp_sym[OF assms(2)]] .

lemma codom_r_acl: "hr ` darts Gr \<subseteq> acl"
  using codom_union by (auto simp: acl_def)

lemma n_comp_d:
  "n_comp (glink Gd) (darts Gd) = (if bGd = [] then 0 else 1) + n_comp (glink G) (darts G - acl)"
proof -
  define Ad where "Ad = {xd \<in> darts Gd. hd xd \<in> acl}"
  have AdD: "Ad \<subseteq> darts Gd" by (auto simp: Ad_def)
  have bAd: "set bGd \<subseteq> Ad"
  proof
    fix b assume b: "b \<in> set bGd"
    then have bD: "b \<in> darts Gd" using bGd_D by blast
    then have "hd b \<in> hr ` darts Gr" using hd_in_r b by simp
    then show "b \<in> Ad" using codom_r_acl bD by (auto simp: Ad_def)
  qed
  have offb: "xd \<notin> set bGd" if "xd \<in> darts Gd - Ad" for xd using that bAd by blast
  \<comment> \<open>Darts outside Ad: their components lift and project faithfully.\<close>
  have stay: "yd \<in> darts Gd - Ad \<and> gcomp G (hd xd) (hd yd)"
    if xd: "xd \<in> darts Gd - Ad" and c: "gcomp Gd xd yd" for xd yd
    using c
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case using xd by simp
  next
    case (step y z)
    have yAd: "y \<in> darts Gd - Ad" and gy: "gcomp G (hd xd) (hd y)" using step(3) by auto
    have yb: "y \<notin> set bGd" by (rule offb[OF yAd])
    have l: "glink G (hd y) (hd z)" using glink_hd_rev[of y z] yAd yb step(2) by blast
    have zD: "z \<in> darts Gd" using step(2) yAd Gd.glink_closed by blast
    have "z \<notin> Ad"
    proof
      assume "z \<in> Ad"
      then have "hd z \<in> acl" by (simp add: Ad_def)
      then have "hd y \<in> acl" using acl_closed_rev r_into_rtranclp[of "glink G", OF l] by blast
      then show False using yAd by (simp add: Ad_def)
    qed
    then show ?case using zD gy l by (auto intro: rtranclp.rtrancl_into_rtrancl)
  qed
  have lift: "gcomp Gd xd yd" if xd: "xd \<in> darts Gd - Ad" and yd: "yd \<in> darts Gd - Ad"
    and c: "gcomp G (hd xd) (hd yd)" for xd yd
  proof -
    obtain P where P: "path (glink G) (hd xd) P" "lastd (hd xd) P = hd yd" using c connect_path by metis
    have walk: "\<exists>w \<in> darts Gd - Ad. lastd (hd u) P' = hd w \<and> gcomp Gd xd w"
      if "path (glink G) (hd u) P'" "u \<in> darts Gd - Ad" "gcomp Gd xd u" for u P'
      using that
    proof (induction P' arbitrary: u)
      case Nil
      then show ?case by auto
    next
      case (Cons z P')
      have ub: "u \<notin> set bGd" by (rule offb[OF Cons.prems(2)])
      have l: "glink G (hd u) z" using Cons.prems(1) by simp
      obtain w where w: "w \<in> darts Gd" "z = hd w" "glink Gd u w"
        using glink_hd[OF _ ub l] Cons.prems(2) by blast
      have cw: "gcomp Gd xd w" by (rule rtranclp.rtrancl_into_rtrancl[OF Cons.prems(3) w(3)])
      have "w \<in> darts Gd - Ad" using stay[OF xd cw] by simp
      moreover have "path (glink G) (hd w) P'" using Cons.prems(1) w(2) by simp
      ultimately show ?case using Cons.IH cw w(2) by simp
    qed
    obtain w where w: "w \<in> darts Gd - Ad" "hd yd = hd w" "gcomp Gd xd w"
      using walk[OF P(1) xd] P(2) by auto
    have "yd = w" using hd_eq yd w by auto
    then show ?thesis using w(3) by simp
  qed
  \<comment> \<open>The darts of Ad form one component when the border is non-empty.\<close>
  have Ad_border: "\<exists>b \<in> set bGd. gcomp Gd xd b" if xd: "xd \<in> Ad" for xd
  proof -
    have xD: "xd \<in> darts Gd" and "hd xd \<in> acl" using xd by (auto simp: Ad_def)
    then obtain y where y: "y \<in> hr ` darts Gr" "gcomp G (hd xd) y" by (auto simp: acl_def)
    obtain P where P: "path (glink G) (hd xd) P" "lastd (hd xd) P = y" using y(2) connect_path by metis
    have walk: "\<exists>b \<in> set bGd. gcomp Gd u b"
      if "path (glink G) (hd u) P'" "lastd (hd u) P' \<in> hr ` darts Gr" "u \<in> darts Gd" for u P'
      using that
    proof (induction P' arbitrary: u)
      case Nil
      then have "u \<in> set bGd" using hd_in_r by simp
      then show ?case by blast
    next
      case (Cons z P')
      show ?case
      proof (cases "u \<in> set bGd")
        case True
        then show ?thesis by blast
      next
        case False
        have l: "glink G (hd u) z" using Cons.prems(1) by simp
        obtain w where w: "w \<in> darts Gd" "z = hd w" "glink Gd u w"
          using glink_hd[OF Cons.prems(3) False l] by blast
        have "\<exists>b \<in> set bGd. gcomp Gd w b"
          using Cons.IH[of w] Cons.prems(1,2) w by simp
        then show ?thesis using w(3) by (meson converse_rtranclp_into_rtranclp)
      qed
    qed
    show ?thesis using walk[OF P(1) _ xD] P(2) y(1) by simp
  qed
  have cardAd: "card (comp_of (glink Gd) ` Ad) = (if bGd = [] then 0 else 1)"
  proof (cases "bGd = []")
    case True
    have "Ad = {}"
    proof (rule ccontr)
      assume "Ad \<noteq> {}"
      then obtain xd where "xd \<in> Ad" by blast
      then show False using Ad_border True by simp
    qed
    then show ?thesis using True by simp
  next
    case False
    obtain b0 where b0: "b0 \<in> set bGd" using False by (cases bGd) auto
    have b0D: "b0 \<in> darts Gd" using b0 bGd_D by blast
    have one: "comp_of (glink Gd) xd = comp_of (glink Gd) b0" if xA: "xd \<in> Ad" for xd
    proof -
      obtain b where b: "b \<in> set bGd" "gcomp Gd xd b" using Ad_border[OF xA] by blast
      have "fconnect (edge Gd) b b0" using bGd_cycle_cedge b b0 by blast
      then have "gcomp Gd b b0" by (rule Gd.cedge_gcomp)
      then have "gcomp Gd xd b0" by (rule rtranclp_trans[OF b(2)])
      then show ?thesis by (simp add: Gd.comp_eq)
    qed
    have "comp_of (glink Gd) ` Ad = {comp_of (glink Gd) b0}"
    proof
      show "comp_of (glink Gd) ` Ad \<subseteq> {comp_of (glink Gd) b0}" using one by blast
      show "{comp_of (glink Gd) b0} \<subseteq> comp_of (glink Gd) ` Ad" using bAd b0 by blast
    qed
    then show ?thesis using False by simp
  qed
  have split_d: "card (comp_of (glink Gd) ` darts Gd) =
      card (comp_of (glink Gd) ` Ad) + card (comp_of (glink Gd) ` (darts Gd - Ad))"
  proof (rule card_classes_split[OF AdD Gd.finite_darts])
    fix x y assume x: "x \<in> Ad" and y: "y \<in> darts Gd - Ad"
    show "comp_of (glink Gd) x \<noteq> comp_of (glink Gd) y"
    proof
      assume "comp_of (glink Gd) x = comp_of (glink Gd) y"
      then have "gcomp Gd y x" using Gd.comp_eq_iff Gd.gcomp_sym by blast
      then have "x \<in> darts Gd - Ad" using stay[OF y] by blast
      then show False using x by simp
    qed
  qed
  have "card (comp_of (glink Gd) ` (darts Gd - Ad)) = card (comp_of (glink G) ` (darts G - acl))"
  proof (rule card_classes_reflect[where h = hd])
    show "comp_of (glink Gd) x = comp_of (glink Gd) y \<longleftrightarrow> comp_of (glink G) (hd x) = comp_of (glink G) (hd y)"
      if x: "x \<in> darts Gd - Ad" and y: "y \<in> darts Gd - Ad" for x y
      unfolding Gd.comp_eq_iff G.comp_eq_iff
    proof
      assume "gcomp Gd x y"
      then show "gcomp G (hd x) (hd y)" using stay[OF x] by blast
    next
      assume "gcomp G (hd x) (hd y)"
      then show "gcomp Gd x y" by (rule lift[OF x y])
    qed
    show "hd ` (darts Gd - Ad) \<subseteq> darts G - acl" using codom_d by (auto simp: Ad_def)
    show "\<And>z. z \<in> darts G - acl \<Longrightarrow> \<exists>x \<in> darts Gd - Ad. comp_of (glink G) (hd x) = comp_of (glink G) z"
    proof -
      fix z assume z: "z \<in> darts G - acl"
      then have "z \<notin> hr ` darts Gr" using codom_r_acl by blast
      then have "z \<in> hd ` darts Gd" using z codom_union by blast
      then obtain w where w: "w \<in> darts Gd" "z = hd w" by blast
      then have "w \<in> darts Gd - Ad" using z by (simp add: Ad_def)
      then show "\<exists>x \<in> darts Gd - Ad. comp_of (glink G) (hd x) = comp_of (glink G) z" using w(2) by blast
    qed
  qed
  then show ?thesis using split_d cardAd by (simp add: n_comp_def)
qed

lemma n_comp_G_split:
  "n_comp (glink G) (darts G) = n_comp (glink G) acl + n_comp (glink G) (darts G - acl)"
  unfolding n_comp_def
proof (rule card_classes_split[OF _ G.finite_darts])
  show "acl \<subseteq> darts G" by (auto simp: acl_def)
  fix x y assume x: "x \<in> acl" and y: "y \<in> darts G - acl"
  show "comp_of (glink G) x \<noteq> comp_of (glink G) y"
  proof
    assume "comp_of (glink G) x = comp_of (glink G) y"
    then have "gcomp G x y" by (simp add: G.comp_eq_iff)
    then have "y \<in> acl" using acl_closed x by blast
    then show False using y by simp
  qed
qed

theorem genus_patch: "genus G = genus Gd + genus Gr"
proof -
  define b :: nat where "b = (if bGd = [] then 0 else 1)"
  have eG: "even_genus G" and ed: "even_genus Gd" and er: "even_genus Gr"
    using even_genusP G.hypermap_axioms Gd.hypermap_axioms Gr.hypermap_axioms by blast+
  have dG: "delta G = delta Gd + delta Gr"
  proof -
    have cardp: "int (card (darts Gd)) + int (card (darts Gr)) = int (length bGd) + int (card (darts G))"
      using card_patch by simp
    have "delta G = 2 * int (n_comp (glink G) (darts G)) + int (card (darts G))
        - int (fcard (edge G) (darts G)) - int (fcard (node G) (darts G)) - int (fcard (face G) (darts G))"
      by (simp add: delta_def Euler_lhs_def Euler_rhs_def)
    moreover have "delta Gd = 2 * int (n_comp (glink Gd) (darts Gd)) + int (card (darts Gd))
        - int (fcard (edge Gd) (darts Gd)) - int (fcard (node Gd) (darts Gd)) - int (fcard (face Gd) (darts Gd))"
      by (simp add: delta_def Euler_lhs_def Euler_rhs_def)
    moreover have "delta Gr = 2 * int (n_comp (glink Gr) (darts Gr)) + int (card (darts Gr))
        - int (fcard (edge Gr) (darts Gr)) - int (fcard (node Gr) (darts Gr)) - int (fcard (face Gr) (darts Gr))"
      by (simp add: delta_def Euler_lhs_def Euler_rhs_def)
    ultimately show ?thesis
      using cardp fcard_G_split fcard_edge_r fcard_edge_d fcard_node_d fcard_node_r fcard_face_r
        fcard_face_d n_comp_r n_comp_d n_comp_G_split by (simp add: b_def)
  qed
  have p: "delta Gd \<ge> 0" "delta Gr \<ge> 0" and ev: "even (delta Gd)"
    using ed er by (simp_all add: even_genus_delta)
  have n: "nat (delta G) = nat (delta Gd) + nat (delta Gr)" using dG p by (simp add: nat_add_distrib)
  obtain k where k: "delta Gd = 2 * k" using ev by (auto elim: evenE)
  have "nat (delta Gd) = 2 * nat k" using k p(1) by (simp add: nat_mult_distrib)
  then have "nat (delta G) div 2 = nat (delta Gd) div 2 + nat (delta Gr) div 2" using n by simp
  then show ?thesis by (simp add: genus_delta)
qed

lemma planar_patch: "planar G \<longleftrightarrow> planar Gd \<and> planar Gr"
  by (simp add: planar_def genus_patch)

subsection \<open>Colourings of patches\<close>

lemma colorable_patch_fwd:
  assumes k: "coloring G k"
  shows "ring_trace Gd bGd (trace (map k bG)) \<and> ring_trace Gr bGr (rot 1 (rev (trace (map k bG))))"
proof -
  have kE: "k (edge G x) \<noteq> k x" and kF: "k (face G x) = k x" if "x \<in> darts G" for x
    using k that by (auto simp: coloring_def)
  have hdD: "hd x \<in> darts G" if "x \<in> darts Gd" for x using codom_d that by blast
  have hrD: "hr x \<in> darts G" if "x \<in> darts Gr" for x using codom_union that by blast
  have kn: "k (node G y) \<noteq> k y" if yD: "y \<in> darts G" for y
  proof -
    have "face G (edge G (node G y)) = y" by (rule G.nodeK)
    then have "k y = k (edge G (node G y))" using kF[of "edge G (node G y)"] yD by simp
    then show ?thesis using kE[of "node G y"] yD by simp
  qed
  have cd: "coloring Gd (k \<circ> hd)" unfolding coloring_def
  proof (intro conjI ballI)
    fix xd assume xd: "xd \<in> darts Gd"
    have c: "G.cface (hd xd) (hd (face Gd xd))" by (rule cFhd[OF xd])
    show "(k \<circ> hd) (face Gd xd) = (k \<circ> hd) xd"
      using G.coloring_cface[OF k c hdD[OF xd]] by simp
    define y where "y = hd (face Gd (edge Gd xd))"
    have exd: "edge Gd xd \<in> darts Gd" using xd by simp
    have yD: "y \<in> darts G" using hdD exd by (simp add: y_def)
    have "hd xd = node G y" using node_d[of "face Gd (edge Gd xd)"] exd by (simp add: Gd.edgeK y_def)
    moreover have "k y = k (hd (edge Gd xd))"
      using G.coloring_cface[OF k cFhd[OF exd] hdD[OF exd]] by (simp add: y_def)
    ultimately show "(k \<circ> hd) (edge Gd xd) \<noteq> (k \<circ> hd) xd" using kn[OF yD] by simp
  qed
  have cr: "coloring Gr (k \<circ> hr)" unfolding coloring_def
  proof (intro conjI ballI)
    fix xr assume xr: "xr \<in> darts Gr"
    show "(k \<circ> hr) (edge Gr xr) \<noteq> (k \<circ> hr) xr" using kE[OF hrD[OF xr]] edge_r[OF xr] by simp
    have fxr: "face Gr xr \<in> darts Gr" using xr by simp
    have "Gr.cface xr (face Gr xr)" using fconnect_step by metis
    then have c: "G.cface (hr xr) (hr (face Gr xr))" using patch_face_r[OF xr fxr] by simp
    have "k (hr (face Gr xr)) = k (hr xr)" by (rule G.coloring_cface[OF k c hrD[OF xr]])
    then show "(k \<circ> hr) (face Gr xr) = (k \<circ> hr) xr" by simp
  qed
  have "trace (map (k \<circ> hd) bGd) = trace (map k bG)" by simp
  moreover have "trace (map (k \<circ> hr) bGr) = rot 1 (rev (trace (map k bG)))"
  proof -
    have "map (k \<circ> hr) bGr = map k (map hr bGr)" by simp
    also have "\<dots> = map k (rev bG)" using map_ring_r by simp
    also have "\<dots> = rev (map k bG)" by (simp add: rev_map)
    finally have "map (k \<circ> hr) bGr = rev (map k bG)" .
    then show ?thesis by (simp add: trace_rev)
  qed
  ultimately show ?thesis using cd cr by (auto simp: ring_trace_def)
qed

lemma colorable_patch_bwd:
  assumes kd: "coloring Gd kd" and kr: "coloring Gr kr"
    and tr: "trace (map kr bGr) = rot 1 (rev (trace (map kd bGd)))"
  shows "four_colorable G"
proof -
  \<comment> \<open>Shift the disk colouring so that it agrees with the remainder on the border.\<close>
  obtain c0 where agree: "rev (map (addc c0 \<circ> kd) bGd) = map kr bGr"
  proof (cases "bGd = []")
    case True
    then have "bGr = []" using length_bGr by auto
    then show ?thesis using that True by simp
  next
    case False
    have ne: "rev (map kd bGd) \<noteq> []" "map kr bGr \<noteq> []" using False length_bGr by auto
    have "trace (rev (map kd bGd)) = trace (map kr bGr)" using tr by (simp add: trace_rev)
    define c where "c = List.hd (rev (map kd bGd)) +c List.hd (map kr bGr)"
    have e1: "rev (map kd bGd) = map (addc c) (map kr bGr)"
      using trace_eq_shift[OF _ ne] \<open>trace (rev (map kd bGd)) = trace (map kr bGr)\<close> by (simp add: c_def)
    have "map (addc c) (rev (map kd bGd)) = map (addc c) (map (addc c) (map kr bGr))" using e1 by simp
    also have "\<dots> = map kr bGr" by (induction bGr) simp_all
    finally have "map (addc c) (rev (map kd bGd)) = map kr bGr" .
    then show ?thesis using that[of c] by (simp add: rev_map comp_def)
  qed
  define kd' where "kd' = addc c0 \<circ> kd"
  have kd'c: "coloring Gd kd'"
    using kd unfolding kd'_def coloring_def by (simp add: addcI)
  have eq_kdr: "kd' xd = kr xr" if xd: "xd \<in> darts Gd" and xr: "xr \<in> darts Gr" and e: "hd xd = hr xr" for xd xr
  proof -
    have xb: "xd \<in> set bGd" using hd_in_r[OF xd] e xr by auto
    then obtain i where i: "i < length bGd" "bGd ! i = xd" by (auto simp: in_set_conv_nth)
    define j where "j = length bGd - 1 - i"
    have j: "j < length bGr" using i length_bGr by (simp add: j_def)
    have "map hr bGr ! j = rev (map hd bGd) ! j" using map_ring_r by simp
    then have "hr (bGr ! j) = hd (bGd ! i)" using j i length_bGr by (simp add: rev_nth j_def)
    then have "hr (bGr ! j) = hr xr" using i e by simp
    moreover have "bGr ! j \<in> darts Gr" using j bGr_D by (meson nth_mem subsetD)
    ultimately have xrj: "bGr ! j = xr" using hr_eq xr by simp
    have "map kr bGr ! j = rev (map kd' bGd) ! j" using agree by (simp add: kd'_def)
    then have "kr (bGr ! j) = kd' (bGd ! i)" using j i length_bGr by (simp add: rev_nth j_def)
    then show ?thesis using xrj i by simp
  qed
  have hdD: "hd x \<in> darts G" if "x \<in> darts Gd" for x using codom_d that by blast
  have hrD: "hr x \<in> darts G" if "x \<in> darts Gr" for x using codom_union that by blast
  define k where "k x = (if x \<in> hr ` darts Gr then kr (inv_into (darts Gr) hr x)
                         else kd' (inv_into (darts Gd) hd x))" for x
  have k_r: "k (hr xr) = kr xr" if "xr \<in> darts Gr" for xr
    using that injr by (simp add: k_def inv_into_f_f)
  have k_d: "k (hd xd) = kd' xd" if xd: "xd \<in> darts Gd" for xd
  proof (cases "hd xd \<in> hr ` darts Gr")
    case True
    then obtain xr where xr: "xr \<in> darts Gr" "hd xd = hr xr" by blast
    then show ?thesis using k_r eq_kdr[OF xd xr(1) xr(2)] by simp
  next
    case False
    then show ?thesis using xd injd by (simp add: k_def inv_into_f_f)
  qed
  have kd'E: "kd' (edge Gd xd) \<noteq> kd' xd" and kd'F: "kd' (face Gd xd) = kd' xd"
    if "xd \<in> darts Gd" for xd using kd'c that by (auto simp: coloring_def)
  have krE: "kr (edge Gr xr) \<noteq> kr xr" and krF: "kr (face Gr xr) = kr xr"
    if "xr \<in> darts Gr" for xr using kr that by (auto simp: coloring_def)
  have "coloring G k" unfolding coloring_def
  proof (intro conjI ballI)
    fix x assume xG: "x \<in> darts G"
    then show "k (edge G x) \<noteq> k x"
    proof (cases rule: dartsG_cases)
      case (r xr)
      have exr: "edge Gr xr \<in> darts Gr" using r(1) by simp
      have "edge G x = hr (edge Gr xr)" using r edge_r by simp
      then have "k (edge G x) = kr (edge Gr xr)" using k_r[OF exr] by simp
      then show ?thesis using r k_r krE by simp
    next
      case (d xd)
      have exd: "edge Gd xd \<in> darts Gd" using d(1) by simp
      have "edge G x = hd (edge Gd xd)" using d edge_d by simp
      then have "k (edge G x) = kd' (edge Gd xd)" using k_d[OF exd] by simp
      then show ?thesis using d k_d kd'E by simp
    qed
    show "k (face G x) = k x"
      using xG
    proof (cases rule: dartsG_cases)
      case (r xr)
      show ?thesis
      proof (cases "face G x \<in> hr ` darts Gr")
        case True
        then obtain yr where yr: "yr \<in> darts Gr" "face G x = hr yr" by blast
        have "G.cface (hr xr) (hr yr)" using r yr fconnect_step by metis
        then have "Gr.cface xr yr" using patch_face_r r(1) yr(1) by simp
        then have "kr yr = kr xr" using Gr.coloring_cface[OF kr] r(1) by blast
        then show ?thesis using r yr k_r by simp
      next
        case False
        have fxG: "face G x \<in> darts G" using xG by simp
        have "face G x \<in> hd ` darts Gd \<union> hr ` darts Gr" using fxG codom_union by simp
        then have "face G x \<in> hd ` darts Gd" using False by blast
        then obtain yd where yd: "yd \<in> darts Gd" "face G x = hd yd" by blast
        define zd where "zd = edge Gd (node Gd yd)"
        have zdD: "zd \<in> darts Gd" using yd(1) by (simp add: zd_def)
        have fz: "face Gd zd = yd" unfolding zd_def by (rule Gd.nodeK)
        have fxr: "face Gr xr \<in> darts Gr" using r(1) by simp
        have nzd: "node Gd zd \<in> darts Gd" using zdD by simp
        \<comment> \<open>hd zd = hr (face xr) by the border relation.\<close>
        have "hd (node Gd yd) = node G (face G x)" using node_d[OF yd(1)] yd(2) by simp
        also have "\<dots> = hr (node Gr (face Gr xr))" using hr_edge_node_face[OF r(1)] r(2) by simp
        finally have "hd zd = hr (face Gr xr)" using hdErN[OF _ fxr, of "node Gd yd"] yd(1) by (simp add: zd_def)
        then have "kd' zd = kr (face Gr xr)" using eq_kdr zdD fxr by blast
        then have "kd' yd = kr xr" using kd'F[OF zdD] fz krF[OF r(1)] by simp
        then show ?thesis using yd k_d r k_r by simp
      qed
    next
      case (d xd)
      have fxd: "face Gd xd \<in> darts Gd" using d(1) by simp
      have "face G x = hd (face Gd xd)" using d hdF by simp
      then have "k (face G x) = kd' (face Gd xd)" using k_d fxd by simp
      then show ?thesis using d k_d kd'F by simp
    qed
  qed
  then show ?thesis by (auto simp: four_colorable_def)
qed

theorem colorable_patch:
  "four_colorable G \<longleftrightarrow> (\<exists>et. ring_trace Gd bGd et \<and> ring_trace Gr bGr (rot 1 (rev et)))"
proof
  assume "four_colorable G"
  then obtain k where "coloring G k" by (auto simp: four_colorable_def)
  then show "\<exists>et. ring_trace Gd bGd et \<and> ring_trace Gr bGr (rot 1 (rev et))"
    using colorable_patch_fwd by blast
next
  assume "\<exists>et. ring_trace Gd bGd et \<and> ring_trace Gr bGr (rot 1 (rev et))"
  then obtain et kd kr where "coloring Gd kd" "et = trace (map kd bGd)"
    "coloring Gr kr" "rot 1 (rev et) = trace (map kr bGr)" by (auto simp: ring_trace_def)
  then show "four_colorable G" using colorable_patch_bwd by metis
qed

subsection \<open>Bridges and connectivity\<close>

lemma patch_bridgeless:
  assumes b: "bridgeless G"
  shows "bridgeless Gd \<and> bridgeless Gr"
proof
  show "bridgeless Gd" unfolding bridgeless_def
  proof (intro ballI notI)
    fix xd assume xd: "xd \<in> darts Gd" and br: "Gd.cface xd (edge Gd xd)"
    define y where "y = hd (face Gd (edge Gd xd))"
    have exd: "edge Gd xd \<in> darts Gd" using xd by simp
    have hx: "hd xd = node G y" using node_d[of "face Gd (edge Gd xd)"] exd by (simp add: Gd.edgeK y_def)
    have "Gd.cface xd (face Gd (edge Gd xd))" using br fconnect_stepI_r by metis
    then have c1: "G.cface (node G y) y" using patch_face_d'[OF xd] hx by (simp add: y_def)
    have "face G (edge G (node G y)) = y" by (rule G.nodeK)
    then have c2: "G.cface (edge G (node G y)) y" using fconnect_step by metis
    have "G.cface (node G y) (edge G (node G y))" by (rule fconnect_trans[OF c1 G.F.fconnect_sym[OF c2]])
    moreover have "node G y \<in> darts G" using hx codom_d xd by force
    ultimately show False using b by (simp add: bridgeless_def)
  qed
  show "bridgeless Gr" unfolding bridgeless_def
  proof (intro ballI notI)
    fix xr assume xr: "xr \<in> darts Gr" and br: "Gr.cface xr (edge Gr xr)"
    have exr: "edge Gr xr \<in> darts Gr" using xr by simp
    have "G.cface (hr xr) (hr (edge Gr xr))" using patch_face_r[OF xr exr] br by simp
    then have "G.cface (hr xr) (edge G (hr xr))" using edge_r[OF xr] by simp
    moreover have "hr xr \<in> darts G" using xr codom_union by blast
    ultimately show False using b by (simp add: bridgeless_def)
  qed
qed

lemma patch_connected_r:
  assumes cc: "connected G" and ne: "darts Gr \<noteq> {}"
  shows "connected Gr"
proof -
  obtain C where C: "comp_of (glink G) ` darts G = {C}"
    using cc by (auto simp: connected_def n_comp_def card_1_singleton_iff)
  have aclD: "acl \<subseteq> darts G" by (auto simp: acl_def)
  obtain x0 where x0: "x0 \<in> darts Gr" using ne by blast
  have "hr x0 \<in> acl" using codom_r_acl x0 by blast
  then have "comp_of (glink G) ` acl = {C}" using C aclD by blast
  then have "n_comp (glink G) acl = 1" by (simp add: n_comp_def)
  then show ?thesis using n_comp_r by (simp add: connected_def)
qed

end

section \<open>Restricting a hypermap to a closed subset\<close>

definition restr :: "'a hypermap \<Rightarrow> 'a set \<Rightarrow> 'a hypermap" where
  "restr G A = \<lparr>darts = A, edge = (\<lambda>x. if x \<in> A then edge G x else x),
                node = (\<lambda>x. if x \<in> A then node G x else x), face = (\<lambda>x. if x \<in> A then face G x else x)\<rparr>"

lemma restr_simps [simp]:
  "darts (restr G A) = A"
  "x \<in> A \<Longrightarrow> edge (restr G A) x = edge G x" "x \<in> A \<Longrightarrow> node (restr G A) x = node G x"
  "x \<in> A \<Longrightarrow> face (restr G A) x = face G x"
  by (simp_all add: restr_def)

context hypermap
begin

lemma hypermap_restr:
  assumes AD: "A \<subseteq> D" and cl: "\<And>x. x \<in> A \<Longrightarrow> e x \<in> A \<and> n x \<in> A \<and> f x \<in> A"
  shows "hypermap (restr G A)"
proof -
  have finA: "finite A" using AD finite_darts by (rule finite_subset)
  have perm: "(\<lambda>x. if x \<in> A then g x else x) permutes A"
    if g: "fperm g D" and clg: "\<And>x. x \<in> A \<Longrightarrow> g x \<in> A" for g
  proof (rule perm_of_inj[OF finA])
    interpret fperm g D by (rule g)
    show "inj_on (\<lambda>x. if x \<in> A then g x else x) A" by (rule inj_onI) simp
  qed (simp_all add: clg)
  show ?thesis
  proof unfold_locales
    show "finite (darts (restr G A))" using finA by simp
    show "edge (restr G A) permutes darts (restr G A)"
      using perm[OF E.fperm_axioms] cl by (simp add: restr_def)
    show "node (restr G A) permutes darts (restr G A)"
      using perm[OF N.fperm_axioms] cl by (simp add: restr_def)
    show "face (restr G A) permutes darts (restr G A)"
      using perm[OF F.fperm_axioms] cl by (simp add: restr_def)
    fix x
    show "node (restr G A) (face (restr G A) (edge (restr G A) x)) = x"
      using cl by (cases "x \<in> A") (simp_all add: restr_def edgeK)
  qed
qed

lemma comp_closed:
  assumes "x \<in> comp_of (glink G) z"
  shows "e x \<in> comp_of (glink G) z \<and> n x \<in> comp_of (glink G) z \<and> f x \<in> comp_of (glink G) z"
  using assms rtranclp.rtrancl_into_rtrancl[of "glink G" z x] by (simp add: comp_of_def)

lemma comp_compl_closed:
  assumes "x \<in> D - comp_of (glink G) z"
  shows "e x \<in> D - comp_of (glink G) z \<and> n x \<in> D - comp_of (glink G) z \<and>
         f x \<in> D - comp_of (glink G) z"
proof -
  have x: "x \<in> D" "\<not> gcomp G z x" using assms by (auto simp: comp_of_def)
  have ny: "\<not> gcomp G z y" if l: "glink G x y" for y
  proof
    assume "gcomp G z y"
    then have "gcomp G z x" by (rule rtranclp_trans[OF _ glink_sym[OF l]])
    then show False using x by simp
  qed
  show ?thesis using ny[of "e x"] ny[of "n x"] ny[of "f x"] x(1) by (simp add: comp_of_def)
qed

lemma patch_comp:
  assumes zD: "z \<in> D"
  shows "patch G (restr G (comp_of (glink G) z)) (restr G (D - comp_of (glink G) z)) id id [] []"
proof -
  let ?C = "comp_of (glink G) z"
  have CD: "?C \<subseteq> D" using zD gcomp_closed by (auto simp: comp_of_def)
  interpret Gd: hypermap "restr G ?C" by (rule hypermap_restr[OF CD comp_closed])
  interpret Gr: hypermap "restr G (D - ?C)" by (rule hypermap_restr[OF _ comp_compl_closed]) blast
  show ?thesis
  proof unfold_locales
    show "id ` darts (restr G ?C) \<subseteq> D" using CD by simp
    show "id ` darts (restr G (D - ?C)) = (D - id ` darts (restr G ?C)) \<union> set (map id [])" by simp
  qed (simp_all add: simple_def comp_closed comp_compl_closed)
qed

theorem minimal_counter_example_is_connected:
  assumes mce: "minimal_counter_example G"
  shows "connected G"
proof (rule ccontr)
  assume ncc: "\<not> connected G"
  have pbpp: "planar_bridgeless_plain_precubic G" and ncol: "\<not> four_colorable G"
    using mce by (simp_all add: minimal_counter_example_def)
  have minG: "\<And>G' :: 'a hypermap. planar_bridgeless_plain_precubic G' \<Longrightarrow> card (darts G') < card D \<Longrightarrow> four_colorable G'"
    using mce unfolding minimal_counter_example_def by blast
  have planG: "planar G" and bG: "bridgeless G" and pG: "plain G"
    using pbpp by (simp_all add: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def planar_bridgeless_def)
  have cG: "cubic G" by (rule minimal_counter_example_is_cubic[OF mce])
  have Dne: "D \<noteq> {}"
  proof
    assume "D = {}"
    then have "coloring G (\<lambda>_. Color0)" by (simp add: coloring_def)
    then show False using ncol by (auto simp: four_colorable_def)
  qed
  then obtain z where zD: "z \<in> D" by blast
  let ?C = "comp_of (glink G) z"
  interpret P: patch G "restr G ?C" "restr G (D - ?C)" id id "[]" "[]" by (rule patch_comp[OF zD])
  have CD: "?C \<subseteq> D" using zD gcomp_closed by (auto simp: comp_of_def)
  have zC: "z \<in> ?C" by (simp add: comp_of_def)
  have CneD: "?C \<noteq> D"
  proof
    assume CD': "?C = D"
    have "comp_of (glink G) ` D = {?C}"
    proof
      show "comp_of (glink G) ` D \<subseteq> {?C}"
      proof
        fix S assume "S \<in> comp_of (glink G) ` D"
        then obtain x where x: "x \<in> D" "S = comp_of (glink G) x" by blast
        then have "gcomp G z x" using CD' by (auto simp: comp_of_def)
        then show "S \<in> {?C}" using x comp_eq by simp
      qed
      show "{?C} \<subseteq> comp_of (glink G) ` D" using zD by blast
    qed
    then show False using ncc by (simp add: connected_def n_comp_def)
  qed
  have card1: "card ?C < card D" using CD CneD finite_darts by (simp add: psubset_card_mono)
  have "D - ?C \<subset> D" using zC zD by blast
  then have card2: "card (D - ?C) < card D" using finite_darts by (simp add: psubset_card_mono)
  have "planar (restr G ?C) \<and> planar (restr G (D - ?C))" using planG P.planar_patch by simp
  moreover have "bridgeless (restr G ?C) \<and> bridgeless (restr G (D - ?C))" using P.patch_bridgeless bG by simp
  moreover have "plain (restr G ?C) \<and> plain (restr G (D - ?C))"
    using P.plain_patch pG by (simp add: plain_def)
  moreover have "cubic (restr G ?C) \<and> cubic (restr G (D - ?C))"
    using P.cubic_patch cG by (simp add: cubic_def)
  ultimately have "planar_bridgeless_plain_precubic (restr G ?C)"
    "planar_bridgeless_plain_precubic (restr G (D - ?C))"
    using P.Gd.hypermap_axioms P.Gr.hypermap_axioms cubic_precubic
    by (auto simp: planar_bridgeless_plain_precubic_def planar_bridgeless_plain_def
        planar_bridgeless_def intro: P.Gd.cubic_precubic P.Gr.cubic_precubic)
  then have "four_colorable (restr G ?C)" "four_colorable (restr G (D - ?C))"
    using minG card1 card2 by simp_all
  then obtain kd kr where "coloring (restr G ?C) kd" "coloring (restr G (D - ?C)) kr"
    by (auto simp: four_colorable_def)
  then have "four_colorable G" using P.colorable_patch_bwd by (simp add: trace_def rot_def)
  then show False using ncol by simp
qed

end

end
