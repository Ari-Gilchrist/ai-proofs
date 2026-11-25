(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfmap.thy
    Configuration maps: construction programs and the pointed maps they build.
    Ported from G. Gonthier's Coq development (cfmap.v).

    Design: Gonthier builds each step on a new finite dart type (ecp_dart G).
    Here every configuration map is a hypermap over nat; a step that adds an
    edge pair uses the two fresh darts Suc (Max D) and Suc (Suc (Max D)), and
    the injections icpU / icpN are the identity.
*)
theory Cfmap
  imports Four_Colour_Maps.Snip Four_Colour_Base.Coloring
begin

section \<open>Construction programs\<close>

datatype cpstep = CpR nat | CpR' | CpY | CpH | CpU | CpK | CpA

type_synonym cprog = "cpstep list"

fun cubic_prog :: "cprog \<Rightarrow> bool" where
  "cubic_prog [] = True"
| "cubic_prog (CpR _ # cp) = cubic_prog cp"
| "cubic_prog (CpU # cp) = cubic_prog cp"
| "cubic_prog (CpY # cp) = cubic_prog cp"
| "cubic_prog (CpH # cp) = cubic_prog cp"
| "cubic_prog _ = False"

datatype config = ConfigRecord (cfsym: bool) (cfcontract_ref: "nat list") (cfprog: cprog)

fun config_prog :: "cprog \<Rightarrow> bool" where
  "config_prog (CpR _ # cp) = config_prog cp"
| "config_prog [CpY] = True"
| "config_prog (CpY # cp) = config_prog cp"
| "config_prog (CpH # cp) = config_prog cp"
| "config_prog _ = False"

lemma config_prog_cubic: "config_prog cp \<Longrightarrow> cubic_prog cp"
  by (induction cp rule: config_prog.induct) simp_all

fun parse_config :: "bool \<Rightarrow> nat list \<Rightarrow> cprog \<Rightarrow> config" where
  "parse_config sy cc (CpR i # cp) = parse_config sy (i # cc) cp"
| "parse_config sy cc cp = ConfigRecord sy (rev cc) cp"

section \<open>Orbits of a permutation as cycles\<close>

context fperm
begin

lemma funpow_inv_cancel: "(f ^^ k) ((inv f ^^ k) z) = z"
  using fun_cong[OF fn_o_inv_fn_is_id[OF bij, of k], of z] by simp

lemma inv_funpow_cancel: "(inv f ^^ k) ((f ^^ k) z) = z"
  using fun_cong[OF inv_fn_o_fn_is_id[OF bij, of k], of z] by simp

lemma funpow_cycle_nth:
  assumes c: "cycle (frel f) p" and i: "i < length p"
  shows "p ! i = (f ^^ i) (hd p)"
  using i
proof (induction i)
  case 0
  then show ?case by (cases p) simp_all
next
  case (Suc i)
  have "f (p ! i) = p ! (Suc i mod length p)" using c Suc.prems by (simp add: cycle_nth)
  then show ?case using Suc by simp
qed

lemma orb_cycle_unique:
  assumes c: "cycle (frel f) (y # q)" and d: "distinct (y # q)"
  shows "orb f y = y # q"
proof -
  define p where "p = y # q"
  have L: "0 < length p" by (simp add: p_def)
  have nth: "p ! i = (f ^^ i) y" if "i < length p" for i
    using funpow_cycle_nth[of p i] c that by (simp add: p_def)
  have bk: "(f ^^ length p) y = y"
  proof -
    have "f (p ! (length p - 1)) = p ! (Suc (length p - 1) mod length p)"
      using c L by (simp add: cycle_nth p_def)
    then have h: "f ((f ^^ (length p - 1)) y) = y" using nth[of "length p - 1"] L by (simp add: p_def)
    obtain m where m: "length p = Suc m" using L by (cases "length p") auto
    show ?thesis using h unfolding m by simp
  qed
  have ord: "order f y = length p"
  proof (rule antisym)
    show "order f y \<le> length p" using bk order_dvd[of "length p" y] L by (simp add: dvd_imp_le)
    show "length p \<le> order f y"
    proof (rule ccontr)
      assume "\<not> length p \<le> order f y"
      then have lt: "order f y < length p" by simp
      have o: "0 < order f y" by (rule order_pos)
      have "p ! order f y = y" using nth[OF lt] by simp
      then have "q ! (order f y - 1) = y" using o by (simp add: p_def nth_Cons')
      moreover have "order f y - 1 < length q" using lt o unfolding p_def length_Cons by linarith
      ultimately have "y \<in> set q" by (metis nth_mem)
      then show False using d by simp
    qed
  qed
  show ?thesis
  proof (rule nth_equalityI)
    show "length (orb f y) = length (y # q)" using ord by (simp add: p_def)
    fix i assume "i < length (orb f y)"
    then have i: "i < length p" using ord by simp
    have "orb f y ! i = (f ^^ i) y" using i ord by (simp add: orb_def traject_def)
    also have "\<dots> = p ! i" using nth[OF i] by simp
    finally show "orb f y ! i = (y # q) ! i" by (simp add: p_def)
  qed
qed

lemma orb_funpow_rot:
  assumes m: "m \<le> order f y"
  shows "orb f ((f ^^ m) y) = rot m (orb f y)"
proof (cases "m = order f y")
  case True
  then show ?thesis by (simp add: rot_def)
next
  case False
  then have m': "m < order f y" using m by simp
  have c: "cycle (frel f) (rot m (orb f y))"
    using cycle_orb[of y] m by (simp add: rot_rotate cycle_rotate)
  have d: "distinct (rot m (orb f y))" by (simp add: distinct_orb)
  have h: "rot m (orb f y) = (f ^^ m) y # tl (rot m (orb f y))"
  proof -
    have "rot m (orb f y) \<noteq> []" using m' by (simp add: rot_def)
    moreover have "hd (rot m (orb f y)) = (f ^^ m) y"
      using m' by (simp add: rot_def orb_def traject_def hd_append hd_drop_conv_nth)
    ultimately show ?thesis by (metis list.collapse)
  qed
  show ?thesis using orb_cycle_unique[of "(f ^^ m) y" "tl (rot m (orb f y))"] c d h by simp
qed

end

section \<open>Rings of pointed maps\<close>

definition cpring :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "cpring G x0 = rev (orb (node G) (node G (node G x0)))"

definition proper_cpring :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "proper_cpring G x0 \<longleftrightarrow> x0 \<noteq> node G x0"

definition long_cpring :: "'a hypermap \<Rightarrow> 'a \<Rightarrow> bool" where
  "long_cpring G x0 \<longleftrightarrow> face G (edge G x0) \<noteq> node G x0"

context hypermap
begin

lemma inv_node_fperm: "fperm (inv n) D"
  by (rule fperm_inv) (simp add: fperm_def node_perm finite_darts)

lemma cpring_inv: "cpring G x0 = orb (inv n) (n x0)"
proof -
  interpret IN: fperm "inv n" D by (rule inv_node_fperm)
  have c: "cycle (frel (inv n)) (cpring G x0)"
  proof -
    have "cycle (frel n) (orb n (n (n x0)))" by (rule N.cycle_orb)
    then have "cycle (\<lambda>a b. n b = a) (cpring G x0)"
      unfolding cpring_def by (simp add: cycle_rev)
    then show ?thesis by (rule cycle_mono[rotated]) (metis N.inv_f)
  qed
  have d: "distinct (cpring G x0)" by (simp add: cpring_def N.distinct_orb)
  have hd: "cpring G x0 = n x0 # tl (cpring G x0)"
  proof -
    have ne: "orb n (n (n x0)) \<noteq> []" using N.order_pos[of "n (n x0)"]
      by (simp add: orb_def traject_def)
    have "last (orb n (n (n x0))) = (n ^^ (order n x0 - 1)) (n (n x0))"
      using N.order_pos[of x0] by (simp add: orb_def traject_def last_map)
    also have "\<dots> = (n ^^ (Suc (order n x0))) x0"
    proof -
      obtain j where j: "order n x0 = Suc j" using N.order_pos[of x0] gr0_implies_Suc by blast
      show ?thesis unfolding j by (simp only: diff_Suc_1 funpow_Suc_right o_apply)
    qed
    also have "\<dots> = n x0" using N.funpow_order[of x0] by simp
    finally show ?thesis using ne unfolding cpring_def
      by (metis hd_rev list.collapse rev_is_Nil_conv)
  qed
  show ?thesis using IN.orb_cycle_unique[of "n x0" "tl (cpring G x0)"] c d hd by simp
qed

lemma cpring_distinct: "distinct (cpring G x0)"
  by (simp add: cpring_def N.distinct_orb)

lemma mem_cpring: "x \<in> set (cpring G x0) \<longleftrightarrow> cnode x0 x"
  by (simp add: cpring_def N.set_orb N.in_cyc_iff)

lemma length_cpring: "length (cpring G x0) = order n x0"
  by (simp add: cpring_def)

lemma cpring_ne: "cpring G x0 \<noteq> []"
proof -
  have "0 < length (cpring G x0)" unfolding length_cpring by (rule N.order_pos)
  then show ?thesis by auto
qed

lemma nth_cpring: "i < order n x0 \<Longrightarrow> cpring G x0 ! i = (inv n ^^ i) (n x0)"
  by (simp add: cpring_inv orb_def traject_def N.order_inv)

lemma size_proper_cpring: "proper_cpring G x0 \<longleftrightarrow> 1 < length (cpring G x0)"
proof -
  have o: "0 < order n x0" by (rule N.order_pos)
  have "proper_cpring G x0 \<longleftrightarrow> order n x0 \<noteq> 1"
    using N.order_1_iff[of x0] by (auto simp: proper_cpring_def)
  also have "\<dots> \<longleftrightarrow> 1 < order n x0" using o by presburger
  finally show ?thesis by (simp add: length_cpring)
qed

lemma nn_eq_iff_order: "n (n x0) = x0 \<longleftrightarrow> order n x0 \<le> 2"
proof
  assume h: "n (n x0) = x0"
  show "order n x0 \<le> 2"
  proof (rule ccontr)
    assume "\<not> order n x0 \<le> 2"
    then have "(n ^^ 2) x0 \<noteq> x0" using N.order_least[of 2 x0] by simp
    then show False using h by (simp add: numeral_2_eq_2)
  qed
next
  assume h: "order n x0 \<le> 2"
  have o: "0 < order n x0" by (rule N.order_pos)
  consider "order n x0 = 1" | "order n x0 = 2" using h o by linarith
  then show "n (n x0) = x0"
  proof cases
    case 1
    then have "n x0 = x0" using N.order_1_iff by simp
    then show ?thesis by simp
  next
    case 2
    then show ?thesis using N.funpow_order[of x0] by (simp add: numeral_2_eq_2)
  qed
qed

lemma size_long_cpring: "long_cpring G x0 \<longleftrightarrow> 2 < length (cpring G x0)"
proof -
  have "long_cpring G x0 \<longleftrightarrow> n (n x0) \<noteq> x0"
    unfolding long_cpring_def using node_eq_iff[of "n x0" x0] by auto
  then show ?thesis using nn_eq_iff_order[of x0] by (simp add: length_cpring not_le)
qed

lemma cycle_rev_cpring: "cycle (frel n) (rev (cpring G x0))"
  by (simp add: cpring_def N.cycle_orb)

lemma cpring_def_char:
  assumes h: "p = n x0 # p'" and d: "distinct p" and c: "cycle (frel n) (rev p)"
  shows "cpring G x0 = p"
proof -
  interpret IN: fperm "inv n" D by (rule inv_node_fperm)
  have "cycle (\<lambda>a b. n b = a) p" using c by (simp add: cycle_rev)
  then have "cycle (frel (inv n)) p" by (rule cycle_mono[rotated]) (metis N.inv_f)
  then show ?thesis using IN.orb_cycle_unique[of "n x0" p'] d h by (simp add: cpring_inv)
qed

lemma head_cpring: "cpring G x0 = n x0 # tl (cpring G x0)"
proof -
  have "hd (cpring G x0) = n x0"
    using nth_cpring[of 0 x0] N.order_pos[of x0] cpring_ne by (simp add: hd_conv_nth)
  then show ?thesis using cpring_ne by (metis list.collapse)
qed

lemma head_long_cpring:
  assumes "long_cpring G x0"
  shows "cpring G x0 = n x0 # x0 # f (e x0) # drop 3 (cpring G x0)"
proof -
  have L: "2 < order n x0" using assms size_long_cpring length_cpring by simp
  have "cpring G x0 = take 3 (cpring G x0) @ drop 3 (cpring G x0)" by simp
  also have "take 3 (cpring G x0) = [n x0, x0, f (e x0)]"
  proof (rule nth_equalityI)
    show "length (take 3 (cpring G x0)) = length [n x0, x0, f (e x0)]"
      using L by (simp add: length_cpring)
    fix i assume "i < length (take 3 (cpring G x0))"
    then have i: "i < 3" by simp
    then consider "i = 0" | "i = 1" | "i = 2" by linarith
    then show "take 3 (cpring G x0) ! i = [n x0, x0, f (e x0)] ! i"
      using L i by cases (simp_all add: nth_cpring numeral_2_eq_2 inv_node_apply nodeK)
  qed
  finally show ?thesis by simp
qed

lemma head_proper_cpring:
  assumes "proper_cpring G x0"
  shows "cpring G x0 = n x0 # x0 # drop 2 (cpring G x0)"
proof -
  have L: "1 < order n x0" using assms size_proper_cpring length_cpring by simp
  have "cpring G x0 = take 2 (cpring G x0) @ drop 2 (cpring G x0)" by simp
  also have "take 2 (cpring G x0) = [n x0, x0]"
  proof (rule nth_equalityI)
    show "length (take 2 (cpring G x0)) = length [n x0, x0]"
      using L by (simp add: length_cpring)
    fix i assume "i < length (take 2 (cpring G x0))"
    then have i: "i < 2" by simp
    then consider "i = 0" | "i = 1" by linarith
    then show "take 2 (cpring G x0) ! i = [n x0, x0] ! i"
      using L i by cases (simp_all add: nth_cpring)
  qed
  finally show ?thesis by simp
qed

lemma connectedD:
  assumes cc: "connected G" and x: "x \<in> D" and y: "y \<in> D"
  shows "gcomp G x y"
proof -
  have "card (comp_of (glink G) ` D) = 1" using cc by (simp add: connected_def n_comp_def)
  then obtain C where C: "comp_of (glink G) ` D = {C}" by (auto simp: card_1_singleton_iff)
  then have "comp_of (glink G) x = comp_of (glink G) y" using x y by blast
  then show ?thesis unfolding comp_of_def by (metis mem_Collect_eq rtranclp.rtrancl_refl)
qed

lemma connectedI:
  assumes a: "a \<in> D" and h: "\<And>x. x \<in> D \<Longrightarrow> gcomp G a x"
  shows "connected G"
proof -
  have "comp_of (glink G) x = comp_of (glink G) a" if x: "x \<in> D" for x
  proof -
    have ax: "gcomp G a x" using h x .
    have xa: "gcomp G x a" using gcomp_sym[OF ax] .
    show ?thesis unfolding comp_of_def
      using rtranclp_trans[OF ax] rtranclp_trans[OF xa] by blast
  qed
  then have "comp_of (glink G) ` D = {comp_of (glink G) a}" using a by blast
  then show ?thesis by (simp add: connected_def n_comp_def)
qed

lemma ucycle_rev_cpring: "ucycle (frel n) (rev (cpring G x0))"
  by (simp add: ucycle_def cycle_rev_cpring cpring_distinct)

lemma ringD_gen: "x0 \<in> D \<Longrightarrow> set (cpring G x0) \<subseteq> D"
  using mem_cpring[of _ x0] N.fconnect_in_D[of x0] by blast

lemma ring_closed_node: "x \<notin> set (cpring G x0) \<Longrightarrow> n x \<notin> set (cpring G x0)"
  by (simp add: mem_cpring)

section \<open>Rotation step\<close>

definition ecpR_ptr :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ecpR_ptr n0 x0 = (n ^^ (order n x0 - n0)) x0"

lemma cpring_ecpR: "cpring G (ecpR_ptr n0 x0) = rot n0 (cpring G x0)"
proof (cases "n0 \<le> order n x0")
  case False
  then show ?thesis by (simp add: ecpR_ptr_def rot_oversize length_cpring)
next
  case True
  interpret IN: fperm "inv n" D by (rule inv_node_fperm)
  have "n (ecpR_ptr n0 x0) = (inv n ^^ n0) (n x0)"
  proof -
    have "(n ^^ n0) (n (ecpR_ptr n0 x0)) = n ((n ^^ n0) ((n ^^ (order n x0 - n0)) x0))"
      by (simp add: ecpR_ptr_def funpow_swap1)
    also have "\<dots> = n ((n ^^ order n x0) x0)"
      using True by (simp only: funpow_add_apply[symmetric] le_add_diff_inverse)
    also have "\<dots> = n x0" by simp
    finally have "(n ^^ n0) (n (ecpR_ptr n0 x0)) = n x0" .
    then have "(inv n ^^ n0) ((n ^^ n0) (n (ecpR_ptr n0 x0))) = (inv n ^^ n0) (n x0)" by simp
    then show ?thesis by (simp only: N.inv_funpow_cancel)
  qed
  then show ?thesis
    using IN.orb_funpow_rot[of n0 "n x0"] True IN.order_inv[of "n x0"]
    by (simp add: cpring_inv N.order_inv)
qed

lemma length_cpring_ecpR: "length (cpring G (ecpR_ptr n0 x0)) = length (cpring G x0)"
  by (simp add: cpring_ecpR)

lemma ecpR_ptr_in: "x0 \<in> D \<Longrightarrow> ecpR_ptr n0 x0 \<in> D"
  by (simp add: ecpR_ptr_def)

end

section \<open>Fresh darts and the U step\<close>

lemma path_frel_cong:
  "path (frel g) x p \<Longrightarrow> (\<And>a. a \<in> set (butlast (x # p)) \<Longrightarrow> g' a = g a) \<Longrightarrow> path (frel g') x p"
  by (induction p arbitrary: x) auto

definition fresh :: "nat set \<Rightarrow> nat" where
  "fresh A = (if A = {} then 0 else Suc (Max A))"

lemma fresh_notin: "finite A \<Longrightarrow> fresh A \<notin> A"
  by (auto simp: fresh_def dest: Max_ge)

lemma fresh_Suc_notin: "finite A \<Longrightarrow> Suc (fresh A) \<notin> A"
  by (auto simp: fresh_def dest: Max_ge)

definition ecpX :: "nat hypermap \<Rightarrow> nat" where
  "ecpX G = fresh (darts G)"

definition ecp_edge :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat" where
  "ecp_edge G x = (if x = ecpX G then Suc (ecpX G) else if x = Suc (ecpX G) then ecpX G else edge G x)"

definition ecpU_node :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ecpU_node G x0 x = (if x = ecpX G then Suc (ecpX G) else if x = Suc (ecpX G) then node G (node G x0)
                       else if x = node G x0 then ecpX G else node G x)"

definition ecpU_face :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ecpU_face G x0 x = (if x = ecpX G then ecpX G else if x = Suc (ecpX G) then node G x0
                       else if face G x = node G x0 then Suc (ecpX G) else face G x)"

definition ecpU :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat hypermap" where
  "ecpU G x0 = \<lparr>darts = darts G \<union> {ecpX G, Suc (ecpX G)}, edge = ecp_edge G,
                node = ecpU_node G x0, face = ecpU_face G x0\<rparr>"

definition ecpN_node :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ecpN_node G x0 x =
     (if x = ecpX G then (if long_cpring G x0 then node G x0 else ecpX G)
      else if x = Suc (ecpX G) then face G (edge G x0)
      else if x = x0 then Suc (ecpX G)
      else if node G (node G x) = x0 then ecpX G else node G x)"

definition ecpN_face :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ecpN_face G x0 x =
     (if x = ecpX G then x0
      else if x = Suc (ecpX G) then
        (if long_cpring G x0 then face G (edge G (face G (edge G x0))) else ecpX G)
      else if x = edge G (face G (edge G x0)) then Suc (ecpX G)
      else if x = edge G (node G x0) then ecpX G else face G x)"

definition ecpN :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat hypermap" where
  "ecpN G x0 = \<lparr>darts = darts G \<union> {ecpX G, Suc (ecpX G)}, edge = ecp_edge G,
                node = ecpN_node G x0, face = ecpN_face G x0\<rparr>"

locale ecp = hypermap G for G :: "nat hypermap" +
  fixes x0 :: nat
  assumes x0D: "x0 \<in> darts G"
begin

abbreviation X where "X \<equiv> ecpX G"
abbreviation Xe where "Xe \<equiv> Suc (ecpX G)"

lemma X_notin [simp]: "X \<notin> D" and Xe_notin [simp]: "Xe \<notin> D"
  by (simp_all add: ecpX_def fresh_notin fresh_Suc_notin finite_darts)

lemma X_neq [simp]: "X \<noteq> Xe" "Xe \<noteq> X" by simp_all

lemma D_neq_X [simp]: "y \<in> D \<Longrightarrow> y \<noteq> X" "y \<in> D \<Longrightarrow> y \<noteq> Xe" "y \<in> D \<Longrightarrow> X \<noteq> y" "y \<in> D \<Longrightarrow> Xe \<noteq> y"
  using X_notin Xe_notin by blast+

lemma nx0D [simp]: "n x0 \<in> D" using x0D by simp

lemma edge_X [simp]: "e X = X" "e Xe = Xe" by (simp_all add: E.out)

lemma perm_eq_X [simp]:
  "e x = X \<longleftrightarrow> x = X" "e x = Xe \<longleftrightarrow> x = Xe"
  "n x = X \<longleftrightarrow> x = X" "n x = Xe \<longleftrightarrow> x = Xe"
  "f x = X \<longleftrightarrow> x = X" "f x = Xe \<longleftrightarrow> x = Xe"
  by (metis E.closed E.out X_notin Xe_notin N.closed N.out F.closed F.out)+

lemma perm_eq_X' [simp]:
  "X = e x \<longleftrightarrow> x = X" "Xe = e x \<longleftrightarrow> x = Xe"
  "X = n x \<longleftrightarrow> x = X" "Xe = n x \<longleftrightarrow> x = Xe"
  "X = f x \<longleftrightarrow> x = X" "Xe = f x \<longleftrightarrow> x = Xe"
  by (metis perm_eq_X)+

lemma nx0_neq [simp]: "n x0 \<noteq> X" "n x0 \<noteq> Xe" "X \<noteq> n x0" "Xe \<noteq> n x0"
    "x0 \<noteq> X" "x0 \<noteq> Xe" "X \<noteq> x0" "Xe \<noteq> x0"
  using nx0D x0D D_neq_X by blast+

lemma ringD: "set (cpring G x0) \<subseteq> D"
  using mem_cpring[of _ x0] N.fconnect_in_D[of x0] x0D by blast
lemma node_X [simp]: "n X = X" "n Xe = Xe" by (simp_all add: N.out)
lemma face_X [simp]: "f X = X" "f Xe = Xe" by (simp_all add: F.out)

definition GU where "GU = ecpU G x0"

lemma GU_simps [simp]:
  "darts GU = D \<union> {X, Xe}"
  "edge GU x = (if x = X then Xe else if x = Xe then X else e x)"
  "node GU x = (if x = X then Xe else if x = Xe then n (n x0) else if x = n x0 then X else n x)"
  "face GU x = (if x = X then X else if x = Xe then n x0 else if f x = n x0 then Xe else f x)"
  by (simp_all add: GU_def ecpU_def ecp_edge_def ecpU_node_def ecpU_face_def)

lemma hypermap_GU: "hypermap GU"
proof -
  have eq: "GU = \<lparr>darts = D \<union> {X, Xe}, edge = edge GU, node = node GU, face = face GU\<rparr>"
    by (simp add: GU_def ecpU_def)
  have c3: "node GU (face GU (edge GU x)) = x" for x
  proof -
    consider "x = X" | "x = Xe" | "x \<noteq> X" "x \<noteq> Xe" by blast
    then show ?thesis
    proof cases
      case 1
      then have "edge GU x = Xe" by simp
      moreover have "face GU Xe = n x0" by simp
      moreover have "node GU (n x0) = X" by simp
      ultimately show ?thesis using 1 by simp
    next
      case 2
      then have "edge GU x = X" by simp
      moreover have "face GU X = X" by simp
      moreover have "node GU X = Xe" by simp
      ultimately show ?thesis using 2 by simp
    next
      case 3
      have E1: "edge GU x = e x" using 3 by simp
      have ex: "e x \<noteq> X" "e x \<noteq> Xe" using 3 by simp_all
      show ?thesis
      proof (cases "f (e x) = n x0")
        case True
        have F1: "face GU (e x) = Xe" using ex True by simp
        have "x = n (n x0)" using edgeK[of x] True by simp
        then show ?thesis unfolding E1 F1 by simp
      next
        case False
        have F1: "face GU (e x) = f (e x)" using ex False by simp
        have fx: "f (e x) \<noteq> X" "f (e x) \<noteq> Xe" using ex by simp_all
        have "node GU (f (e x)) = n (f (e x))" using fx False by simp
        then show ?thesis unfolding E1 F1 by (simp only: edgeK)
      qed
    qed
  qed
  have cl: "edge GU x \<in> D \<union> {X, Xe} \<and> node GU x \<in> D \<union> {X, Xe} \<and> face GU x \<in> D \<union> {X, Xe}"
    if h: "x \<in> D \<union> {X, Xe}" for x
  proof -
    consider "x \<in> D" | "x = X" | "x = Xe" using h by blast
    then show ?thesis by cases (simp_all add: x0D)
  qed
  have out: "edge GU x = x \<and> node GU x = x \<and> face GU x = x" if "x \<notin> D \<union> {X, Xe}" for x
  proof -
    have "x \<notin> D" "x \<noteq> X" "x \<noteq> Xe" using that by auto
    moreover have "x \<noteq> n x0" using that nx0D by blast
    ultimately show ?thesis by (simp add: E.out N.out F.out)
  qed
  have "hypermap \<lparr>darts = D \<union> {X, Xe}, edge = edge GU, node = node GU, face = face GU\<rparr>"
    by (rule hypermap_cancel3[OF _ cl out c3]) (simp add: finite_darts)
  then show ?thesis unfolding eq[symmetric] .
qed

sublocale U: hypermap GU by (rule hypermap_GU)

lemma skip_face_GU: "skip Xe (face GU) = f"
proof
  fix x
  show "skip Xe (face GU) x = f x"
  proof (cases "x = Xe")
    case False
    then show ?thesis
      by (cases "x = X"; cases "f x = n x0") (simp_all add: skip_def)
  qed (simp add: skip_def)
qed

lemma skip_node_GU: "skip X (skip Xe (node GU)) = n"
proof
  fix x
  show "skip X (skip Xe (node GU)) x = n x"
    by (cases "x = X"; cases "x = Xe"; cases "x = n x0") (simp_all add: skip_def)
qed

lemma cpring_GU: "cpring GU X = Xe # X # cpring G x0"
proof (rule U.cpring_def_char)
  show "Xe # X # cpring G x0 = node GU X # X # cpring G x0" by simp
  show "distinct (Xe # X # cpring G x0)"
    using cpring_distinct[of x0] ringD by auto
  define q where "q = orb n (n (n x0))"
  have rq: "rev (cpring G x0) = q" by (simp add: cpring_def q_def)
  have cq: "cycle (frel n) q" unfolding q_def by (rule N.cycle_orb)
  have dq: "distinct q" unfolding q_def by (rule N.distinct_orb)
  obtain a q1 where q: "q = a # q1" unfolding q_def using N.orb_Cons by blast
  have a: "a = n (n x0)" using q N.orb_Cons[of "n (n x0)"] unfolding q_def by simp
  have pq: "path (frel n) a (q1 @ [a])" using cq q by (simp add: cycle_Cons)
  have lastq: "last (a # q1) = n x0"
  proof -
    have "hd (cpring G x0) = n x0" using head_cpring[of x0] by (metis list.sel(1))
    moreover have "last q = hd (cpring G x0)" unfolding rq[symmetric] using cpring_ne by (simp add: last_rev)
    ultimately show ?thesis using q by simp
  qed
  have inq: "set q \<subseteq> D" unfolding q_def using N.set_orb N.cyc_subset x0D by (metis N.closed)
  have bl: "a' \<noteq> n x0" if "a' \<in> set (butlast (a # q1))" for a'
  proof
    assume "a' = n x0"
    then have "n x0 \<in> set (butlast (a # q1))" using that by simp
    moreover have "distinct (butlast (a # q1) @ [last (a # q1)])"
      using dq q by (metis append_butlast_last_id list.distinct(1))
    ultimately show False using lastq by simp
  qed
  have p1: "path (frel (node GU)) a q1"
  proof (rule path_frel_cong[of n])
    show "path (frel n) a q1" using pq by simp
    fix a' assume a': "a' \<in> set (butlast (a # q1))"
    have "a' \<in> D" using a' inq q by (meson in_set_butlastD subsetD)
    then show "node GU a' = n a'" using bl[OF a'] by simp
  qed
  have "rev (Xe # X # cpring G x0) = a # q1 @ [X, Xe]" using rq q by simp
  moreover have "path (frel (node GU)) a (q1 @ [X, Xe, a])"
    using p1 lastq a by simp
  ultimately show "cycle (frel (node GU)) (rev (Xe # X # cpring G x0))" by (simp add: cycle_Cons)
qed

lemma length_cpring_GU: "length (cpring GU X) = Suc (Suc (length (cpring G x0)))"
  by (simp add: cpring_GU)

lemma plain_GU:
  assumes "plain G"
  shows "plain GU"
proof -
  have h: "\<forall>x\<in>D. e (e x) = x \<and> e x \<noteq> x" using assms plainP by (simp add: plain_def)
  have "\<forall>x\<in>darts GU. edge GU (edge GU x) = x \<and> edge GU x \<noteq> x"
  proof
    fix x assume "x \<in> darts GU"
    then consider "x \<in> D" | "x = X" | "x = Xe" by auto
    then show "edge GU (edge GU x) = x \<and> edge GU x \<noteq> x"
      by cases (use h in auto)
  qed
  then show ?thesis unfolding plain_def U.plainP .
qed

lemma cface_GU_old:
  assumes "x \<in> D" "y \<in> D"
  shows "fconnect (face GU) x y \<longleftrightarrow> cface x y"
proof -
  interpret UF: fperm "face GU" "D \<union> {X, Xe}" using U.F.fperm_axioms by simp
  have "cyc (skip Xe (face GU)) x = cyc (face GU) x - {Xe}"
    using assms by (intro UF.cyc_skip) auto
  then have "cyc f x = cyc (face GU) x - {Xe}" by (simp add: skip_face_GU)
  then show ?thesis using assms by (auto simp: UF.in_cyc_iff[symmetric] F.in_cyc_iff[symmetric])
qed

lemma cface_GU_X: "fconnect (face GU) X y \<longleftrightarrow> y = X"
proof -
  have "((face GU) ^^ k) X = X" for k by (induction k) simp_all
  then show ?thesis by (auto simp: fconnect_def)
qed

lemma cface_GU_Xe: "fconnect (face GU) Xe (n x0)"
  using fconnect_step[of "face GU" Xe] by simp

lemma adj_GU_old:
  assumes "x \<in> D" "y \<in> D"
  shows "adj GU x y \<longleftrightarrow> adj G x y"
proof
  assume "adj GU x y"
  then obtain z where z: "fconnect (face GU) x z" "fconnect (face GU) (edge GU z) y"
    by (auto simp: adj_def rlink_def)
  have zD: "z \<in> D \<union> {X, Xe}" using U.F.fconnect_in_D[OF z(1)] assms by simp
  have zX: "z \<noteq> X"
  proof
    assume "z = X"
    then have "fconnect (face GU) X x" using U.F.fconnect_sym[OF z(1)] by simp
    then show False using cface_GU_X assms by simp
  qed
  have zXe: "z \<noteq> Xe"
  proof
    assume "z = Xe"
    then have "fconnect (face GU) X y" using z(2) by simp
    then show False using cface_GU_X assms by simp
  qed
  have zD': "z \<in> D" using zD zX zXe by simp
  have "cface x z" using z(1) cface_GU_old assms zD' by simp
  moreover have "cface (e z) y" using z(2) cface_GU_old assms zD' zX zXe by simp
  ultimately show "adj G x y" by (auto simp: adj_def rlink_def)
next
  assume "adj G x y"
  then obtain z where z: "cface x z" "cface (e z) y" by (auto simp: adj_def rlink_def)
  have zD: "z \<in> D" using F.fconnect_in_D[OF z(1)] assms by simp
  have "fconnect (face GU) x z" using z(1) cface_GU_old assms zD by simp
  moreover have "fconnect (face GU) (edge GU z) y" using z(2) cface_GU_old assms zD by simp
  ultimately show "adj GU x y" unfolding adj_def rlink_def by blast
qed

lemma adj_GU_X: "adj GU X u \<longleftrightarrow> fconnect (face GU) (n x0) u"
proof -
  have "adj GU X u \<longleftrightarrow> fconnect (face GU) Xe u"
    by (auto simp: adj_def rlink_def cface_GU_X)
  also have "\<dots> \<longleftrightarrow> fconnect (face GU) (n x0) u"
  proof
    assume "fconnect (face GU) Xe u"
    then show "fconnect (face GU) (n x0) u" by (rule fconnect_trans[OF U.F.fconnect_sym[OF cface_GU_Xe]])
  next
    assume "fconnect (face GU) (n x0) u"
    then show "fconnect (face GU) Xe u" by (rule fconnect_trans[OF cface_GU_Xe])
  qed
  finally show ?thesis .
qed

lemma bridgeless_GU: "bridgeless G \<Longrightarrow> bridgeless GU"
  unfolding bridgeless_def
proof (intro ballI)
  fix x assume bG: "\<forall>x\<in>D. \<not> cface x (e x)" and x: "x \<in> darts GU"
  show "\<not> fconnect (face GU) x (edge GU x)"
  proof (cases "x \<in> D")
    case True
    then show ?thesis using bG cface_GU_old[of x "e x"] by simp
  next
    case False
    then have "x = X \<or> x = Xe" using x by simp
    then show ?thesis
    proof
      assume "x = X"
      then show ?thesis using cface_GU_X[of Xe] by simp
    next
      assume xe: "x = Xe"
      show ?thesis
      proof
        assume "fconnect (face GU) x (edge GU x)"
        then have "fconnect (face GU) X Xe" using xe U.F.fconnect_sym by simp
        then show False using cface_GU_X[of Xe] by simp
      qed
    qed
  qed
qed

lemma fcard_face_GU: "fcard (face GU) (darts GU) = Suc (fcard f D)"
proof -
  interpret UF: fperm "face GU" "D \<union> {X, Xe}" using U.F.fperm_axioms by simp
  have "fcard (skip Xe (face GU)) (D \<union> {X, Xe} - {Xe}) + (if face GU Xe = Xe then 1 else 0)
        = fcard (face GU) (D \<union> {X, Xe})" by (rule UF.fcard_skip) simp
  then have "fcard f (insert X D) = fcard (face GU) (darts GU)"
    by (simp add: skip_face_GU insert_Diff_if)
  moreover have "fcard f (insert X D) = Suc (fcard f D)"
  proof -
    have "cyc f X = {X}" by (simp add: F.cyc_out)
    moreover have "{X} \<notin> cyc f ` D" using F.x_in_cyc F.cyc_subset by fastforce
    ultimately show ?thesis using finite_darts by (simp add: fcard_def card_insert_if)
  qed
  ultimately show ?thesis by simp
qed

lemma card_GU: "card (darts GU) = Suc (Suc (card D))"
  using finite_darts by simp

lemma quasicubic_GU:
  assumes q: "quasicubic G (rev (cpring G x0))"
  shows "quasicubic GU (rev (cpring GU X))"
proof -
  have h: "\<forall>x\<in>D - set (cpring G x0). n (n (n x)) = x \<and> n x \<noteq> x"
    using q cubicP by (simp add: quasicubic_def)
  have "\<forall>x\<in>darts GU - set (cpring GU X). node GU (node GU (node GU x)) = x \<and> node GU x \<noteq> x"
  proof
    fix x assume x: "x \<in> darts GU - set (cpring GU X)"
    then have xD: "x \<in> D" and xr: "x \<notin> set (cpring G x0)" by (auto simp: cpring_GU)
    have r1: "n x \<notin> set (cpring G x0)" and r2: "n (n x) \<notin> set (cpring G x0)"
      using xr ring_closed_node by blast+
    have nr: "n x0 \<in> set (cpring G x0)" using head_cpring[of x0] by (metis list.set_intros(1))
    have a: "x \<noteq> n x0" "n x \<noteq> n x0" "n (n x) \<noteq> n x0" using xr r1 r2 nr by auto
    show "node GU (node GU (node GU x)) = x \<and> node GU x \<noteq> x"
      using h xD xr a by simp
  qed
  then show ?thesis unfolding quasicubic_def U.cubicP by simp
qed

lemma glink_GU: "glink G u v \<Longrightarrow> u \<in> D \<Longrightarrow> gcomp GU u v"
proof -
  assume g: "glink G u v" and u: "u \<in> D"
  consider "e u = v" | "n u = v" | "f u = v" using g by (auto simp: glink_def)
  then show "gcomp GU u v"
  proof cases
    case 1
    then have "glink GU u v" using u by (simp add: glink_def)
    then show ?thesis by blast
  next
    case 2
    show ?thesis
    proof (cases "u = n x0")
      case True
      have "glink GU u X" "glink GU X Xe" "glink GU Xe v" using True 2 by (simp_all add: glink_def)
      then show ?thesis by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
    next
      case False
      then have "glink GU u v" using u 2 by (simp add: glink_def)
      then show ?thesis by blast
    qed
  next
    case 3
    show ?thesis
    proof (cases "f u = n x0")
      case True
      have "glink GU u Xe" "glink GU Xe v" using True 3 u by (simp_all add: glink_def)
      then show ?thesis by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
    next
      case False
      then have "glink GU u v" using u 3 by (simp add: glink_def)
      then show ?thesis by blast
    qed
  qed
qed

lemma gcomp_GU: "gcomp G u v \<Longrightarrow> u \<in> D \<Longrightarrow> gcomp GU u v"
proof (induction rule: rtranclp_induct)
  case (step y z)
  have "y \<in> D" using step.hyps(1) step.prems gcomp_closed by blast
  then show ?case using step glink_GU[of y z] by (meson rtranclp_trans)
qed simp

lemma connected_GU:
  assumes cc: "connected G"
  shows "connected GU"
proof (rule U.connectedI[of x0])
  show "x0 \<in> darts GU" using x0D by simp
  have old: "gcomp GU x0 y" if "y \<in> D" for y
    using gcomp_GU[OF connectedD[OF cc x0D that] x0D] .
  fix y assume y: "y \<in> darts GU"
  have "gcomp GU x0 X"
  proof -
    have "glink GU (n x0) X" by (simp add: glink_def)
    then show ?thesis using old[of "n x0"] by (meson rtranclp.rtrancl_into_rtrancl nx0D)
  qed
  moreover have "gcomp GU x0 Xe"
  proof -
    have "glink GU X Xe" by (simp add: glink_def)
    then show ?thesis using \<open>gcomp GU x0 X\<close> by (meson rtranclp.rtrancl_into_rtrancl)
  qed
  ultimately show "gcomp GU x0 y" using y old by auto
qed


lemma planar_GU:
  assumes pl: "planar G" and plainG: "plain G" and q: "quasicubic G (rev (cpring G x0))"
    and cc: "connected G"
  shows "planar GU"
proof -
  have geoG: "ucycle_plain_quasicubic_connected G (rev (cpring G x0))"
    using hypermap_axioms plainG q cc ucycle_rev_cpring ringD
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
  have geoU: "ucycle_plain_quasicubic_connected GU (rev (cpring GU X))"
    using hypermap_GU plain_GU[OF plainG] quasicubic_GU[OF q] connected_GU[OF cc]
      U.ucycle_rev_cpring[of X] U.ringD_gen
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
  have eG: "6 * (1 + fcard f D) = card D + (2 * length (cpring G x0) + 12)"
    using quasicubic_Euler[OF geoG] pl cpring_ne[of x0] by simp
  show ?thesis
    using U.quasicubic_Euler[OF geoU] eG fcard_face_GU card_GU length_cpring_GU U.cpring_ne[of X] by simp
qed

section \<open>The N step\<close>

definition GN where "GN = ecpN G x0"

abbreviation lng where "lng \<equiv> long_cpring G x0"

lemma GN_simps [simp]:
  "darts GN = D \<union> {X, Xe}"
  "edge GN x = (if x = X then Xe else if x = Xe then X else e x)"
  "node GN x = (if x = X then (if lng then n x0 else X) else if x = Xe then f (e x0)
               else if x = x0 then Xe else if n (n x) = x0 then X else n x)"
  "face GN x = (if x = X then x0 else if x = Xe then (if lng then f (e (f (e x0))) else X)
               else if x = e (f (e x0)) then Xe else if x = e (n x0) then X else f x)"
  by (simp_all add: GN_def ecpN_def ecp_edge_def ecpN_node_def ecpN_face_def)

lemma fe_eq_x0: "f (e y) = x0 \<longleftrightarrow> y = n x0"
  by (metis nodeK edgeK)

lemma efe_D [simp]: "e (f (e x0)) \<in> D" "e (n x0) \<in> D" "f (e x0) \<in> D" "f (e (f (e x0))) \<in> D"
  using x0D by simp_all

lemma not_lng: "\<not> lng \<longleftrightarrow> f (e x0) = n x0"
  by (simp add: long_cpring_def)

lemma hypermap_GN: "hypermap GN"
proof -
  have eq: "GN = \<lparr>darts = D \<union> {X, Xe}, edge = edge GN, node = node GN, face = face GN\<rparr>"
    by (simp add: GN_def ecpN_def)
  have c3: "node GN (face GN (edge GN x)) = x" for x
  proof -
    consider "x = X" | "x = Xe" | "x \<noteq> X" "x \<noteq> Xe" by blast
    then show ?thesis
    proof cases
      case 1
      show ?thesis
      proof (cases lng)
        case True
        define y where "y = f (e (f (e x0)))"
        have F1: "face GN (edge GN x) = y" using 1 True by (simp add: y_def)
        have yD: "y \<in> D" using x0D by (simp add: y_def)
        have yx0: "y \<noteq> x0" using True fe_eq_x0[of "f (e x0)"] not_lng by (simp add: y_def)
        have nny: "n (n y) = x0" by (simp add: y_def edgeK)
        show ?thesis unfolding F1 using yD yx0 nny 1 by simp
      next
        case False
        then show ?thesis using 1 by simp
      qed
    next
      case 2
      then show ?thesis by simp
    next
      case 3
      have E1: "edge GN x = e x" using 3 by simp
      have ex: "e x \<noteq> X" "e x \<noteq> Xe" using 3 by simp_all
      show ?thesis
      proof (cases "x = f (e x0)")
        case True
        have "face GN (e x) = Xe" using ex True by simp
        then show ?thesis unfolding E1 using True by simp
      next
        case nf: False
        have ne1: "e x \<noteq> e (f (e x0))" using nf by simp
        show ?thesis
        proof (cases "x = n x0")
          case True
          have lg: lng using nf True not_lng by simp
          have "face GN (e x) = X" using ex ne1 True by simp
          then show ?thesis unfolding E1 using True lg by simp
        next
          case nn: False
          have ne2: "e x \<noteq> e (n x0)" using nn by simp
          have F1: "face GN (e x) = f (e x)" using ex ne1 ne2 by simp
          have fx: "f (e x) \<noteq> X" "f (e x) \<noteq> Xe" using ex by simp_all
          have fx0: "f (e x) \<noteq> x0" using nn fe_eq_x0 by simp
          have nnf: "n (n (f (e x))) \<noteq> x0"
          proof
            assume "n (n (f (e x))) = x0"
            then have "n x = x0" by (simp add: edgeK)
            then have "x = f (e x0)" by (metis nodeK)
            then show False using nf by simp
          qed
          show ?thesis unfolding E1 F1 using fx fx0 nnf by (simp add: edgeK)
        qed
      qed
    qed
  qed
  have cl: "edge GN x \<in> D \<union> {X, Xe} \<and> node GN x \<in> D \<union> {X, Xe} \<and> face GN x \<in> D \<union> {X, Xe}"
    if h: "x \<in> D \<union> {X, Xe}" for x
  proof -
    consider "x \<in> D" | "x = X" | "x = Xe" using h by blast
    then show ?thesis by cases (simp_all add: x0D)
  qed
  have out: "edge GN x = x \<and> node GN x = x \<and> face GN x = x" if h: "x \<notin> D \<union> {X, Xe}" for x
  proof -
    have a: "x \<notin> D" "x \<noteq> X" "x \<noteq> Xe" using h by auto
    have b: "x \<noteq> x0" "x \<noteq> e (f (e x0))" "x \<noteq> e (n x0)" using a x0D efe_D by auto
    have c: "n (n x) \<noteq> x0" using a(1) x0D N.out[OF a(1)] by auto
    show ?thesis using a b c by (simp add: E.out N.out F.out)
  qed
  have "hypermap \<lparr>darts = D \<union> {X, Xe}, edge = edge GN, node = node GN, face = face GN\<rparr>"
    by (rule hypermap_cancel3[OF _ cl out c3]) (simp add: finite_darts)
  then show ?thesis unfolding eq[symmetric] .
qed

sublocale NN: hypermap GN by (rule hypermap_GN)

lemma plain_GN: "plain G \<Longrightarrow> plain GN"
proof -
  assume "plain G"
  then have h: "\<forall>x\<in>D. e (e x) = x \<and> e x \<noteq> x" using plainP by (simp add: plain_def)
  have "\<forall>x\<in>darts GN. edge GN (edge GN x) = x \<and> edge GN x \<noteq> x"
  proof
    fix x assume "x \<in> darts GN"
    then consider "x \<in> D" | "x = X" | "x = Xe" by auto
    then show "edge GN (edge GN x) = x \<and> edge GN x \<noteq> x" by cases (use h in auto)
  qed
  then show ?thesis unfolding plain_def NN.plainP .
qed

lemma skip_face_GN: "skip X (skip Xe (face GN)) = f"
proof
  fix x
  have fX: "face GN X = x0" by simp
  show "skip X (skip Xe (face GN)) x = f x"
  proof (cases "x = X \<or> x = Xe")
    case True
    then show ?thesis by (auto simp: skip_def)
  next
    case False
    then have xX: "x \<noteq> X" "x \<noteq> Xe" by auto
    show ?thesis
    proof (cases "x = e (f (e x0))")
      case True
      show ?thesis
      proof (cases lng)
        case True
        then show ?thesis using xX \<open>x = e (f (e x0))\<close> by (simp add: skip_def nodeK)
      next
        case False
        then have "f x = x0" using \<open>x = e (f (e x0))\<close> not_lng by (simp add: nodeK)
        then show ?thesis using xX \<open>x = e (f (e x0))\<close> False by (simp add: skip_def nodeK)
      qed
    next
      case ne1: False
      show ?thesis
      proof (cases "x = e (n x0)")
        case True
        then have "f x = x0" by (simp add: nodeK)
        then show ?thesis using xX ne1 True by (simp add: skip_def nodeK)
      next
        case False
        then show ?thesis using xX ne1 by (simp add: skip_def nodeK)
      qed
    qed
  qed
qed

lemma cyc_face_GN_old:
  assumes "x \<in> D"
  shows "cyc f x = cyc (face GN) x - {X, Xe}"
proof -
  interpret NF: fperm "face GN" "D \<union> {X, Xe}" using NN.F.fperm_axioms by simp
  interpret NF2: fperm "skip Xe (face GN)" "D \<union> {X, Xe} - {Xe}" by (rule NF.fperm_skip)
  have "cyc (skip X (skip Xe (face GN))) x = cyc (skip Xe (face GN)) x - {X}"
    using assms by (intro NF2.cyc_skip) auto
  moreover have "cyc (skip Xe (face GN)) x = cyc (face GN) x - {Xe}"
    using assms by (intro NF.cyc_skip) auto
  ultimately show ?thesis by (auto simp: skip_face_GN)
qed

lemma cface_GN_old:
  assumes "x \<in> D" "y \<in> D"
  shows "fconnect (face GN) x y \<longleftrightarrow> cface x y"
  using cyc_face_GN_old[OF assms(1)] assms
  by (auto simp: NN.F.in_cyc_iff[symmetric] F.in_cyc_iff[symmetric])

lemma cface_GN_X: "fconnect (face GN) X x0"
  using fconnect_step[of "face GN" X] by simp

lemma cface_GN_Xe: "fconnect (face GN) Xe (e (f (e x0)))"
  using NN.F.fconnect_sym[OF fconnect_step[of "face GN" "e (f (e x0))"]] by simp

lemma fband_GN: "u \<in> darts GN \<Longrightarrow> \<exists>x \<in> D. fconnect (face GN) u x"
  using cface_GN_X cface_GN_Xe x0D by (auto intro: fconnect_refl)

lemma fcard_face_GN: "fcard (face GN) (darts GN) = fcard f D"
proof -
  interpret NF: fperm "face GN" "D \<union> {X, Xe}" using NN.F.fperm_axioms by simp
  interpret NF2: fperm "skip Xe (face GN)" "D \<union> {X, Xe} - {Xe}" by (rule NF.fperm_skip)
  have a: "fcard (skip Xe (face GN)) (D \<union> {X, Xe} - {Xe}) + (if face GN Xe = Xe then 1 else 0)
        = fcard (face GN) (D \<union> {X, Xe})" by (rule NF.fcard_skip) simp
  have b: "fcard (skip X (skip Xe (face GN))) (D \<union> {X, Xe} - {Xe} - {X})
           + (if skip Xe (face GN) X = X then 1 else 0)
        = fcard (skip Xe (face GN)) (D \<union> {X, Xe} - {Xe})" by (rule NF2.fcard_skip) simp
  have fXe: "face GN Xe \<noteq> Xe" by simp
  have sX: "skip Xe (face GN) X \<noteq> X" by (simp add: skip_def)
  have Dd: "insert X (insert Xe D) - {Xe} - {X} = D" by auto
  show ?thesis using a b fXe sX by (simp add: skip_face_GN Dd)
qed

lemma card_GN: "card (darts GN) = Suc (Suc (card D))"
  using finite_darts by simp

lemma adj_GN_old:
  assumes x: "x \<in> D" and y: "y \<in> D"
  shows "adj GN x y \<longleftrightarrow> adj G x y \<or> (cface (e (f (e x0))) x \<and> cface x0 y)
                        \<or> (cface (e (f (e x0))) y \<and> cface x0 x)"
proof
  assume "adj GN x y"
  then obtain z where z: "fconnect (face GN) x z" "fconnect (face GN) (edge GN z) y"
    unfolding adj_def rlink_def by blast
  have zD: "z \<in> D \<union> {X, Xe}" using NN.F.fconnect_in_D[OF z(1)] x by simp
  then consider "z \<in> D" | "z = X" | "z = Xe" by blast
  then show "adj G x y \<or> (cface (e (f (e x0))) x \<and> cface x0 y) \<or> (cface (e (f (e x0))) y \<and> cface x0 x)"
  proof cases
    case 1
    have "cface x z" using z(1) cface_GN_old x 1 by simp
    moreover have "cface (e z) y" using z(2) cface_GN_old y 1 by simp
    ultimately show ?thesis unfolding adj_def rlink_def by blast
  next
    case 2
    have "fconnect (face GN) x x0" using fconnect_trans[OF z(1)] cface_GN_X 2 by simp
    then have a: "cface x0 x" using cface_GN_old x x0D F.fconnect_sym by blast
    have "fconnect (face GN) (e (f (e x0))) y"
      using fconnect_trans[OF NN.F.fconnect_sym[OF cface_GN_Xe]] z(2) 2 by simp
    then have "cface (e (f (e x0))) y" using cface_GN_old[OF efe_D(1) y] by simp
    then show ?thesis using a by blast
  next
    case 3
    have "fconnect (face GN) x (e (f (e x0)))" using fconnect_trans[OF z(1)] cface_GN_Xe 3 by simp
    then have a: "cface (e (f (e x0))) x" using cface_GN_old[OF x efe_D(1)] F.fconnect_sym by blast
    have "fconnect (face GN) x0 y"
      using fconnect_trans[OF NN.F.fconnect_sym[OF cface_GN_X]] z(2) 3 by simp
    then have "cface x0 y" using cface_GN_old y x0D by simp
    then show ?thesis using a by blast
  qed
next
  assume "adj G x y \<or> (cface (e (f (e x0))) x \<and> cface x0 y) \<or> (cface (e (f (e x0))) y \<and> cface x0 x)"
  then consider "adj G x y" | "cface (e (f (e x0))) x" "cface x0 y" | "cface (e (f (e x0))) y" "cface x0 x"
    by blast
  then show "adj GN x y"
  proof cases
    case 1
    then obtain z where z: "cface x z" "cface (e z) y" unfolding adj_def rlink_def by blast
    have zD: "z \<in> D" using F.fconnect_in_D[OF z(1)] x by simp
    have "fconnect (face GN) x z" using z(1) cface_GN_old x zD by simp
    moreover have "fconnect (face GN) (edge GN z) y" using z(2) cface_GN_old y zD by simp
    ultimately show ?thesis unfolding adj_def rlink_def by blast
  next
    case 2
    have "fconnect (face GN) x (e (f (e x0)))" using F.fconnect_sym[OF 2(1)] cface_GN_old[OF x efe_D(1)] by simp
    then have "fconnect (face GN) x Xe" by (rule fconnect_trans[OF _ NN.F.fconnect_sym[OF cface_GN_Xe]])
    moreover have "fconnect (face GN) (edge GN Xe) y"
      using fconnect_trans[OF cface_GN_X] 2(2) cface_GN_old y x0D by simp
    ultimately show ?thesis unfolding adj_def rlink_def by blast
  next
    case 3
    have "fconnect (face GN) x x0" using F.fconnect_sym[OF 3(2)] cface_GN_old x x0D by simp
    then have "fconnect (face GN) x X" by (rule fconnect_trans[OF _ NN.F.fconnect_sym[OF cface_GN_X]])
    moreover have "fconnect (face GN) (edge GN X) y"
      using fconnect_trans[OF cface_GN_Xe] 3(1) cface_GN_old[OF efe_D(1) y] by simp
    ultimately show ?thesis unfolding adj_def rlink_def by blast
  qed
qed

lemma nn_eq_x0: "n (n s) = x0 \<longleftrightarrow> s = f (e (f (e x0)))"
  by (metis edgeK nodeK)

lemma lng_proper: "lng \<Longrightarrow> x0 \<noteq> n x0"
  using size_long_cpring size_proper_cpring proper_cpring_def by fastforce

lemma cpring_GN_long:
  assumes lg: lng
  shows "cpring GN X = n x0 # X # drop 3 (cpring G x0)"
proof (rule NN.cpring_def_char)
  define fe where "fe = f (e x0)"
  define rest where "rest = drop 3 (cpring G x0)"
  have ring: "cpring G x0 = n x0 # x0 # fe # rest"
    unfolding fe_def rest_def by (rule head_long_cpring[OF lg])
  have dr: "distinct (n x0 # x0 # fe # rest)" using cpring_distinct[of x0] ring by simp
  have rD: "set rest \<subseteq> D" using ringD ring by auto
  have prp: "x0 \<noteq> n x0" by (rule lng_proper[OF lg])
  show "n x0 # X # rest = node GN X # X # rest" using lg by simp
  show "distinct (n x0 # X # rest)" using dr rD by auto
  have cq: "cycle (frel n) (rev rest @ [fe, x0, n x0])"
    using cycle_rev_cpring[of x0] ring by simp
  show "cycle (frel (node GN)) (rev (n x0 # X # rest))"
  proof (cases "rev rest")
    case Nil
    have "n (n x0) = fe" using cq Nil by (simp add: cycle_Cons)
    then have n3: "n (n (n x0)) = x0" by (simp add: fe_def edgeK)
    have "node GN (n x0) = X" using n3 prp[symmetric] by simp
    then show ?thesis using Nil lg by (simp add: cycle_Cons)
  next
    case (Cons b rr1)
    have pq: "path (frel n) b (rr1 @ [fe, x0, n x0, b])" using cq Cons by (simp add: cycle_Cons)
    have nfe: "n (lastd b rr1) = fe" using pq by simp
    have nnl: "n (n (lastd b rr1)) = x0" using nfe by (simp add: fe_def edgeK)
    have nb: "n (n x0) = b" using pq by simp
    have rr: "set (b # rr1) = set rest" using Cons by (metis set_rev)
    have drr: "distinct (b # rr1)" using Cons dr by (metis distinct.simps(2) distinct_rev)
    have bD: "set (b # rr1) \<subseteq> D" using rr rD by simp
    have x0r: "x0 \<notin> set (b # rr1)" "fe \<notin> set (b # rr1)" "n x0 \<notin> set (b # rr1)" using rr dr by auto
    have lD: "lastd b rr1 \<in> set (b # rr1)" by (rule lastd_in)
    have p1: "path (frel (node GN)) b rr1"
    proof (rule path_frel_cong[of n])
      show "path (frel n) b rr1" using pq by simp
      fix a assume a: "a \<in> set (butlast (b # rr1))"
      have a': "a \<in> set (b # rr1)" using a by (rule in_set_butlastD)
      have aD: "a \<in> D" "a \<noteq> x0" using a' bD x0r by auto
      have "a \<noteq> lastd b rr1"
      proof
        assume "a = lastd b rr1"
        moreover have "distinct (butlast (b # rr1) @ [last (b # rr1)])"
          using drr by (metis append_butlast_last_id list.distinct(1))
        ultimately show False using a by simp
      qed
      then have "n (n a) \<noteq> x0" using nnl nn_eq_x0 by metis
      then show "node GN a = n a" using aD by simp
    qed
    have lD': "lastd b rr1 \<in> D" using lD bD by blast
    have lx0: "lastd b rr1 \<noteq> x0" using lD x0r(1) by blast
    have g1: "node GN (lastd b rr1) = X" using lD' lx0 nnl by simp
    have g2: "node GN X = n x0" using lg by simp
    have g3: "node GN (n x0) = b"
    proof -
      have "n (n (n x0)) \<noteq> x0"
      proof
        assume "n (n (n x0)) = x0"
        then have "b = fe" using nb by (metis fe_def nodeK)
        then show False using x0r by simp
      qed
      then show ?thesis using nb prp[symmetric] by simp
    qed
    have "rev (n x0 # X # rest) = b # rr1 @ [X, n x0]" using Cons by simp
    moreover have "path (frel (node GN)) b (rr1 @ [X, n x0, b])" using p1 g1 g2 g3 by simp
    ultimately show ?thesis by (simp add: cycle_Cons)
  qed
qed

lemma cpring_GN_short: "\<not> lng \<Longrightarrow> cpring GN X = [X]"
  by (rule NN.cpring_def_char) (simp_all add: cycle_Cons)

lemma length_cpring_GN:
  assumes "proper_cpring G x0"
  shows "length (cpring GN X) = length (cpring G x0) - 1"
proof (cases lng)
  case True
  then show ?thesis using cpring_GN_long size_long_cpring by simp
next
  case False
  then show ?thesis using cpring_GN_short assms size_long_cpring size_proper_cpring by simp
qed

lemma quasicubic_GN:
  assumes q: "quasicubic G (rev (cpring G x0))" and pr: "proper_cpring G x0"
  shows "quasicubic GN (rev (cpring GN X))"
proof -
  define fe where "fe = f (e x0)"
  have prp: "x0 \<noteq> n x0" using pr by (simp add: proper_cpring_def)
  have h: "\<forall>x\<in>D - set (cpring G x0). n (n (n x)) = x \<and> n x \<noteq> x"
    using q cubicP by (simp add: quasicubic_def)
  have feD: "fe \<in> D" using x0D by (simp add: fe_def)
  have fex0: "fe \<noteq> x0" using prp fe_eq_x0[of x0] by (auto simp: fe_def)
  have nfe: "n fe = x0" by (simp add: fe_def edgeK)
  have tri: "node GN Xe = fe" "node GN fe = x0" "node GN x0 = Xe"
  proof -
    show "node GN Xe = fe" by (simp add: fe_def)
    have "n (n fe) \<noteq> x0" using nfe prp by simp
    then show "node GN fe = x0" using feD fex0 nfe by simp
    show "node GN x0 = Xe" by simp
  qed
  have ring_old: "u \<in> set (cpring G x0) \<Longrightarrow> u \<notin> set (cpring GN X) \<Longrightarrow> u = x0 \<or> u = fe" for u
  proof -
    assume u: "u \<in> set (cpring G x0)" and u': "u \<notin> set (cpring GN X)"
    show ?thesis
    proof (cases lng)
      case True
      obtain rest where r: "cpring G x0 = n x0 # x0 # fe # rest" "cpring GN X = n x0 # X # rest"
        using head_long_cpring[OF True] cpring_GN_long[OF True] unfolding fe_def by blast
      show ?thesis using u u' unfolding r by auto
    next
      case False
      have L2: "length (cpring G x0) = 2"
        using False pr size_long_cpring size_proper_cpring by simp
      obtain rest where r: "cpring G x0 = n x0 # x0 # rest"
        using head_proper_cpring[OF pr] by blast
      have "rest = []" using L2 unfolding r by simp
      moreover have "n x0 = fe" using False not_lng by (simp add: fe_def)
      ultimately show ?thesis using u unfolding r by auto
    qed
  qed
  have "\<forall>u\<in>darts GN - set (cpring GN X). node GN (node GN (node GN u)) = u \<and> node GN u \<noteq> u"
  proof
    fix u assume u: "u \<in> darts GN - set (cpring GN X)"
    have uX: "u \<noteq> X"
    proof (cases lng)
      case True then show ?thesis using u cpring_GN_long by auto
    next
      case False then show ?thesis using u cpring_GN_short by auto
    qed
    consider "u = Xe" | "u = x0" | "u = fe" | "u \<in> D" "u \<notin> set (cpring G x0)"
      using u uX ring_old by auto
    then show "node GN (node GN (node GN u)) = u \<and> node GN u \<noteq> u"
    proof cases
      case 1 then show ?thesis using tri feD by auto
    next
      case 2 then show ?thesis using tri feD by auto
    next
      case 3 then show ?thesis using tri feD fex0 by auto
    next
      case 4
      have r1: "n u \<notin> set (cpring G x0)" "n (n u) \<notin> set (cpring G x0)"
        using 4 ring_closed_node by blast+
      have x0r: "x0 \<in> set (cpring G x0)" "fe \<in> set (cpring G x0)"
        by (simp_all add: mem_cpring fe_def inv_node_apply[symmetric])
      have ne: "u \<noteq> x0" "n u \<noteq> x0" "n (n u) \<noteq> x0" using 4 r1 x0r by auto
      have nn: "n (n u) \<noteq> x0" "n (n (n u)) \<noteq> x0" "n (n (n (n u))) \<noteq> x0"
      proof -
        have l: "f (e fe) \<in> set (cpring G x0)" by (simp add: mem_cpring fe_def inv_node_apply[symmetric])
        show "n (n u) \<noteq> x0" "n (n (n u)) \<noteq> x0" "n (n (n (n u))) \<noteq> x0"
          using 4 r1 l nn_eq_x0 ring_closed_node by (metis fe_def)+
      qed
      show ?thesis using h 4 ne nn by simp
    qed
  qed
  then show ?thesis unfolding quasicubic_def NN.cubicP by simp
qed

lemma glink_GN:
  assumes g: "glink G u v" and u: "u \<in> D"
  shows "gcomp GN u v"
proof -
  have step: "glink GN a b \<Longrightarrow> gcomp GN a b" for a b by blast
  have two: "glink GN a b \<Longrightarrow> glink GN b c \<Longrightarrow> gcomp GN a c" for a b c
    by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
  have three: "glink GN a b \<Longrightarrow> glink GN b c \<Longrightarrow> glink GN c d \<Longrightarrow> gcomp GN a d" for a b c d
    by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
  consider "e u = v" | "n u = v" | "f u = v" using g by (auto simp: glink_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using u by (intro step) (simp add: glink_def)
  next
    case 2
    show ?thesis
    proof (cases "u = x0")
      case True
      show ?thesis
      proof (cases lng)
        case lg: True
        have a: "glink GN X x0" "glink GN X (n x0)" using lg by (simp_all add: glink_def)
        have "gcomp GN x0 X" using NN.gcomp_sym[OF step[OF a(1)]] .
        then show ?thesis using True 2 step[OF a(2)] by (meson rtranclp_trans)
      next
        case False
        have "glink GN x0 Xe" "glink GN Xe (n x0)" using False not_lng by (simp_all add: glink_def)
        then have "gcomp GN x0 (n x0)" by (rule two)
        then show ?thesis using True 2 by simp
      qed
    next
      case ux0: False
      show ?thesis
      proof (cases "n (n u) = x0")
        case True
        have nu: "n u = f (e x0)" using True by (metis nodeK)
        have "glink GN u X" "glink GN X Xe" "glink GN Xe v"
          using u ux0 True nu 2 by (simp_all add: glink_def)
        then show ?thesis by (intro three)
      next
        case False
        then show ?thesis using u ux0 2 by (intro step) (simp add: glink_def)
      qed
    qed
  next
    case 3
    show ?thesis
    proof (cases "u = e (f (e x0))")
      case True
      show ?thesis
      proof (cases lng)
        case lg: True
        have "glink GN u Xe" "glink GN Xe v" using True lg 3 by (simp_all add: glink_def)
        then show ?thesis by (intro two)
      next
        case False
        have fv: "v = x0" using 3 True False not_lng by (simp add: nodeK)
        have "glink GN u Xe" "glink GN Xe X" "glink GN X v" using True False fv by (simp_all add: glink_def)
        then show ?thesis by (intro three)
      qed
    next
      case ne1: False
      show ?thesis
      proof (cases "u = e (n x0)")
        case True
        have fv: "v = x0" using 3 True by (simp add: nodeK)
        have "glink GN u X" "glink GN X v" using True ne1 fv by (simp_all add: glink_def)
        then show ?thesis by (intro two)
      next
        case False
        then show ?thesis using u ne1 3 by (intro step) (simp add: glink_def)
      qed
    qed
  qed
qed

lemma gcomp_GN: "gcomp G u v \<Longrightarrow> u \<in> D \<Longrightarrow> gcomp GN u v"
proof (induction rule: rtranclp_induct)
  case (step y z)
  have "y \<in> D" using step.hyps(1) step.prems gcomp_closed by blast
  then show ?case using step glink_GN[of y z] by (meson rtranclp_trans)
qed simp

lemma connected_GN:
  assumes cc: "connected G"
  shows "connected GN"
proof (rule NN.connectedI[of x0])
  show "x0 \<in> darts GN" using x0D by simp
  have old: "gcomp GN x0 y" if "y \<in> D" for y
    using gcomp_GN[OF connectedD[OF cc x0D that] x0D] .
  have gX: "gcomp GN x0 X"
  proof -
    have "glink GN X x0" by (simp add: glink_def)
    then show ?thesis using NN.gcomp_sym by blast
  qed
  have gXe: "gcomp GN x0 Xe"
  proof -
    have "glink GN x0 Xe" by (simp add: glink_def)
    then show ?thesis by blast
  qed
  fix y assume y: "y \<in> darts GN"
  then show "gcomp GN x0 y" using old gX gXe by auto
qed

lemma planar_GN:
  assumes pl: "planar G" and plainG: "plain G" and q: "quasicubic G (rev (cpring G x0))"
    and cc: "connected G" and pr: "proper_cpring G x0"
  shows "planar GN"
proof -
  have geoG: "ucycle_plain_quasicubic_connected G (rev (cpring G x0))"
    using hypermap_axioms plainG q cc ucycle_rev_cpring ringD
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
  have geoN: "ucycle_plain_quasicubic_connected GN (rev (cpring GN X))"
    using hypermap_GN plain_GN[OF plainG] quasicubic_GN[OF q pr] connected_GN[OF cc]
      NN.ucycle_rev_cpring[of X] NN.ringD_gen[of X]
    by (simp add: ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def plain_quasicubic_def)
  have eG: "6 * (1 + fcard f D) = card D + (2 * length (cpring G x0) + 12)"
    using quasicubic_Euler[OF geoG] pl cpring_ne[of x0] by simp
  have L: "2 \<le> length (cpring G x0)" using pr size_proper_cpring by simp
  show ?thesis
    using NN.quasicubic_Euler[OF geoN] eG fcard_face_GN card_GN length_cpring_GN[OF pr]
      NN.cpring_ne[of X] L by simp
qed

end

end
