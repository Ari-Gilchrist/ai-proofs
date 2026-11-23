(*  
    Title:      Koenig_Edge_Colouring.thy
    Author:     Ari Gilchrist

    This formalisation was developed with substantial assistance from Anthropic's Claude Opus 5.5,
    which drafted the definitions, proofs and documentation. The author reviewed the development,
    revised the accompanying text, and verified that the definitions and theorem statements
    capture the intended mathematics.
*)

section \<open>K\H{o}nig's Theorem\<close>

theory Koenig_Edge_Colouring
  imports "Undirected_Graph_Theory.Bipartite_Graphs"
begin

subsection \<open>Proper edge colourings\<close>

text \<open>
  An `edge colouring' \<open>c\<close> assigns each edge of a set \<open>E'\<close> one of \<open>k\<close> colours.
  It is `proper' if no two edges which share a vertex are assigned the same colour.
\<close>

definition proper_colouring_on :: "'a edge set \<Rightarrow> ('a edge \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "proper_colouring_on E' c k \<longleftrightarrow>
     (\<forall>e\<in>E'. c e < k) \<and> (\<forall>e1\<in>E'. \<forall>e2\<in>E'. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 \<noteq> {} \<longrightarrow> c e1 \<noteq> c e2)"

lemma proper_colouring_onI:
  assumes "\<And>e. e \<in> E' \<Longrightarrow> c e < k"
    and "\<And>e1 e2 v. e1 \<in> E' \<Longrightarrow> e2 \<in> E' \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> v \<in> e1 \<Longrightarrow> v \<in> e2 \<Longrightarrow> c e1 \<noteq> c e2"
  shows "proper_colouring_on E' c k"
  using assms unfolding proper_colouring_on_def by blast

lemma proper_colouring_onD:
  assumes "proper_colouring_on E' c k"
  shows "e \<in> E' \<Longrightarrow> c e < k"
    and "e1 \<in> E' \<Longrightarrow> e2 \<in> E' \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> v \<in> e1 \<Longrightarrow> v \<in> e2 \<Longrightarrow> c e1 \<noteq> c e2"
  using assms unfolding proper_colouring_on_def by blast+

lemma proper_colouring_on_empty [simp]: "proper_colouring_on {} c k"
  by (simp add: proper_colouring_on_def)

lemma proper_colouring_on_mono:
  "proper_colouring_on E' c k \<Longrightarrow> E'' \<subseteq> E' \<Longrightarrow> proper_colouring_on E'' c k"
  unfolding proper_colouring_on_def by blast

lemma proper_colouring_on_more_colours:
  "proper_colouring_on E' c k \<Longrightarrow> k \<le> k' \<Longrightarrow> proper_colouring_on E' c k'"
  unfolding proper_colouring_on_def by fastforce

text \<open>The edges of \<open>E'\<close> at a vertex \<open>v\<close>.\<close>

definition edges_at :: "'a edge set \<Rightarrow> 'a \<Rightarrow> 'a edge set" where
  "edges_at E' v = {e \<in> E'. v \<in> e}"

lemma edges_at_mono: "E' \<subseteq> E'' \<Longrightarrow> edges_at E' v \<subseteq> edges_at E'' v"
  unfolding edges_at_def by blast

lemma finite_edges_at [intro]: "finite E' \<Longrightarrow> finite (edges_at E' v)"
  unfolding edges_at_def by simp

lemma edges_at_insert_in: "v \<in> e \<Longrightarrow> edges_at (insert e E') v = insert e (edges_at E' v)"
  unfolding edges_at_def by blast

text \<open>
  In a proper colouring, the edges at a vertex receive pairwise distinct
  colours, so there are at most \<open>k\<close> of them.
\<close>

lemma proper_colouring_on_inj_on_edges_at:
  assumes "proper_colouring_on E' c k"
  shows "inj_on c (edges_at E' v)"
  using proper_colouring_onD(2)[OF assms] unfolding edges_at_def inj_on_def by blast

lemma proper_colouring_on_card_edges_at:
  assumes "proper_colouring_on E' c k"
  shows "card (edges_at E' v) \<le> k"
proof -
  have "c ` edges_at E' v \<subseteq> {0..<k}"
    using proper_colouring_onD(1)[OF assms] unfolding edges_at_def by auto
  then have "card (c ` edges_at E' v) \<le> k"
    using card_mono[of "{0..<k}"] by fastforce
  then show ?thesis
    using proper_colouring_on_inj_on_edges_at[OF assms] card_image by metis
qed

text \<open>If fewer than \<open>k\<close> edges meet a vertex, some colour below \<open>k\<close> is missing there.\<close>

lemma missing_colour:
  assumes "finite S" "card S < k"
  obtains \<alpha> where "\<alpha> < k" "\<alpha> \<notin> c ` S"
proof -
  have "card (c ` S) < card {0..<k}"
    using card_image_le[OF assms(1), of c] assms(2) by simp
  then have "\<not> {0..<k} \<subseteq> c ` S"
    using card_mono[OF finite_imageI[OF assms(1)]] by fastforce
  then obtain \<alpha> where "\<alpha> \<in> {0..<k}" "\<alpha> \<notin> c ` S"
    by blast
  then show ?thesis
    using that by simp
qed

text \<open>
  Suppose a colour is not used on any edge that shares a vertex with a new
  edge \<open>e\<close>. Then \<open>e\<close> can be given that colour, and the colouring remains proper.
\<close>

lemma proper_colouring_on_insert:
  assumes "proper_colouring_on E' c k" "e \<notin> E'" "\<alpha> < k"
    and "\<And>e'. e' \<in> E' \<Longrightarrow> e' \<inter> e \<noteq> {} \<Longrightarrow> c e' \<noteq> \<alpha>"
  shows "proper_colouring_on (insert e E') (c(e := \<alpha>)) k"
proof (rule proper_colouring_onI)
  fix e' assume "e' \<in> insert e E'"
  then show "(c(e := \<alpha>)) e' < k"
    using assms(1,3) proper_colouring_onD(1) by (cases "e' = e") auto
next
  fix e1 e2 v
  assume e12: "e1 \<in> insert e E'" "e2 \<in> insert e E'" "e1 \<noteq> e2" "v \<in> e1" "v \<in> e2"
  show "(c(e := \<alpha>)) e1 \<noteq> (c(e := \<alpha>)) e2"
  proof (cases "e1 = e")
    case True
    then have "e2 \<in> E'" "e2 \<noteq> e" using e12 by auto
    then show ?thesis using True assms(4)[of e2] e12 by auto
  next
    case e1: False
    show ?thesis
    proof (cases "e2 = e")
      case True
      then have "e1 \<in> E'" using e12 e1 by auto
      then show ?thesis using True e1 assms(4)[of e1] e12 by auto
    next
      case False
      then show ?thesis
        using e1 e12 proper_colouring_onD(2)[OF assms(1)] by auto
    qed
  qed
qed

subsection \<open>Swapping colours along an alternating chain\<close>

text \<open>
  We fix a set of edges \<open>E'\<close> between two disjoint vertex sets \<open>X\<close> and \<open>Y\<close>,
  a colouring \<open>c\<close> of \<open>E'\<close> in which adjacent edges have distinct colours,
  two distinct colours \<open>a\<close> and \<open>b\<close>, and a vertex \<open>y \<in> Y\<close> at which colour
  \<open>b\<close> is missing.
\<close>

locale alternating_chain =
  fixes E' :: "'a edge set"
    and c :: "'a edge \<Rightarrow> nat"
    and a b :: nat
    and y :: 'a
    and X Y :: "'a set"
  assumes distinct: "\<And>e1 e2 v. e1 \<in> E' \<Longrightarrow> e2 \<in> E' \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> v \<in> e1 \<Longrightarrow> v \<in> e2
                       \<Longrightarrow> c e1 \<noteq> c e2"
    and between: "\<And>e. e \<in> E' \<Longrightarrow> \<exists>p q. e = {p, q} \<and> p \<in> X \<and> q \<in> Y"
    and disjoint: "X \<inter> Y = {}"
    and y_in_Y: "y \<in> Y"
    and a_neq_b: "a \<noteq> b"
    and b_missing_at_y: "\<And>e. e \<in> E' \<Longrightarrow> y \<in> e \<Longrightarrow> c e \<noteq> b"
begin

text \<open>The colour of the \<open>i\<close>-th edge of an alternating walk: \<open>a, b, a, b, \<dots>\<close>\<close>

definition col :: "nat \<Rightarrow> nat" where
  "col i = (if even i then a else b)"

lemma col_0 [simp]: "col 0 = a"
  and col_1 [simp]: "col (Suc 0) = b"
  and col_Suc_Suc [simp]: "col (Suc (Suc i)) = col i"
  by (simp_all add: col_def)

lemma col_cases: "col i = a \<or> col i = b"
  by (simp add: col_def)

lemma col_Suc_neq: "col (Suc i) \<noteq> col i"
  using a_neq_b by (simp add: col_def)

lemma col_eq_b_iff: "col i = b \<longleftrightarrow> odd i"
  using a_neq_b by (simp add: col_def)

text \<open>
  \<^term>\<open>reach i v\<close> holds if there is an alternating walk of length \<open>i\<close> from
  \<open>y\<close> to \<open>v\<close> whose edges are coloured \<open>col 0, col 1, \<dots>, col (i - 1)\<close>.
  Note that the walk need not be a path; this frees us from having to argue
  about simple or maximal paths.
\<close>

inductive reach :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
  reach_0: "reach 0 y"
| reach_Suc: "reach i u \<Longrightarrow> {u, w} \<in> E' \<Longrightarrow> c {u, w} = col i \<Longrightarrow> reach (Suc i) w"

lemma reach_0_iff: "reach 0 v \<longleftrightarrow> v = y"
  by (auto elim: reach.cases intro: reach_0)

lemma reach_SucE:
  assumes "reach (Suc i) w"
  obtains u where "reach i u" "{u, w} \<in> E'" "c {u, w} = col i"
  using assms by (cases rule: reach.cases) auto

lemma edge_endpoints:
  assumes "e \<in> E'" "v \<in> e"
  obtains w where "e = {v, w}"
  using between[OF assms(1)] assms(2) by (auto simp: insert_commute)

text \<open>Since the graph is bipartite, the side of a reachable vertex is determined by parity.\<close>

lemma reach_parity:
  assumes "reach i v"
  shows "(even i \<longrightarrow> v \<in> Y) \<and> (odd i \<longrightarrow> v \<in> X)"
  using assms
proof (induction rule: reach.induct)
  case reach_0
  then show ?case using y_in_Y by simp
next
  case (reach_Suc i u w)
  from between[OF reach_Suc.hyps(2)] obtain p q where pq: "{u, w} = {p, q}" "p \<in> X" "q \<in> Y"
    by blast
  then have "(u = p \<and> w = q) \<or> (u = q \<and> w = p)"
    by (auto simp: doubleton_eq_iff)
  then show ?case
    using reach_Suc.IH pq(2,3) disjoint by auto
qed

lemma reach_even_in_Y: "reach i v \<Longrightarrow> even i \<Longrightarrow> v \<in> Y"
  and reach_odd_in_X: "reach i v \<Longrightarrow> odd i \<Longrightarrow> v \<in> X"
  using reach_parity by blast+

text \<open>The chain: all edges traversed by some alternating walk from \<open>y\<close>.\<close>

definition chain :: "'a edge set" where
  "chain = {{u, w} | i u w. reach i u \<and> {u, w} \<in> E' \<and> c {u, w} = col i}"

lemma chainI: "reach i u \<Longrightarrow> {u, w} \<in> E' \<Longrightarrow> c {u, w} = col i \<Longrightarrow> {u, w} \<in> chain"
  unfolding chain_def by blast

lemma chainE:
  assumes "e \<in> chain"
  obtains i u w where "e = {u, w}" "reach i u" "{u, w} \<in> E'" "c {u, w} = col i"
  using assms unfolding chain_def by blast

lemma chain_subset: "chain \<subseteq> E'"
  by (auto elim: chainE)

lemma chain_colour:
  assumes "e \<in> chain"
  shows "c e = a \<or> c e = b"
  using assms by (rule chainE) (auto simp: col_def)

text \<open>
  The key closure property: if an edge of the chain meets another edge
  coloured \<open>a\<close> or \<open>b\<close>, then that edge also belongs to the chain.
\<close>

lemma chain_closed:
  assumes e1: "e1 \<in> chain" and e2: "e2 \<in> E'" "e1 \<noteq> e2" "v \<in> e1" "v \<in> e2"
    and c2: "c e2 = a \<or> c e2 = b"
  shows "e2 \<in> chain"
proof -
  obtain i u w where e1_def: "e1 = {u, w}" "reach i u" "{u, w} \<in> E'" "c {u, w} = col i"
    using e1 by (rule chainE)
  have "c e2 \<noteq> c e1"
    using distinct[OF e2(1) chain_subset[THEN subsetD, OF e1]] e2 by auto
  then have c2_col: "c e2 = col (Suc i)"
    using c2 e1_def(1,4) a_neq_b by (auto simp: col_def)
  obtain z where e2_def: "e2 = {v, z}"
    using edge_endpoints[OF e2(1,4)] .
  from e2(3) e1_def(1) have "v = w \<or> v = u" by auto
  then show ?thesis
  proof
    assume "v = w"
    have "reach (Suc i) w"
      using reach_Suc e1_def(2-4) by blast
    then show ?thesis
      using chainI[of "Suc i" v z] e2_def e2(1) c2_col \<open>v = w\<close> by simp
  next
    assume vu: "v = u"
    show ?thesis
    proof (cases i)
      case 0
      then have "v = y"
        using e1_def(2) vu by (simp add: reach_0_iff)
      moreover have "c e2 = b"
        using c2_col 0 by simp
      ultimately show ?thesis
        using b_missing_at_y e2(1,4) by blast
    next
      case (Suc j)
      then obtain u' where u': "reach j u'" "{u', u} \<in> E'" "c {u', u} = col j"
        using e1_def(2) by (auto elim: reach_SucE)
      have "c {u', u} = c e2"
        using u'(3) c2_col Suc by simp
      then have "{u', u} = e2"
        using distinct[OF u'(2) e2(1)] vu e2(4) by blast
      then show ?thesis
        using chainI[OF u'] by simp
    qed
  qed
qed

text \<open>Swapping colours \<open>a\<close> and \<open>b\<close> on the chain.\<close>

definition swap :: "'a edge \<Rightarrow> nat" where
  "swap e = (if e \<in> chain then (if c e = a then b else a) else c e)"

lemma swap_distinct:
  assumes "e1 \<in> E'" "e2 \<in> E'" "e1 \<noteq> e2" "v \<in> e1" "v \<in> e2"
  shows "swap e1 \<noteq> swap e2"
proof -
  have neq: "c e1 \<noteq> c e2"
    using distinct assms by blast
  consider "e1 \<in> chain" "e2 \<in> chain" | "e1 \<notin> chain" "e2 \<notin> chain"
    | "e1 \<in> chain" "e2 \<notin> chain" | "e1 \<notin> chain" "e2 \<in> chain"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using neq chain_colour[of e1] chain_colour[of e2] a_neq_b by (auto simp: swap_def)
  next
    case 2
    then show ?thesis using neq by (simp add: swap_def)
  next
    case 3
    then have "c e2 \<noteq> a \<and> c e2 \<noteq> b"
      using chain_closed[of e1 e2 v] assms by blast
    then show ?thesis using 3 by (auto simp: swap_def)
  next
    case 4
    then have "c e1 \<noteq> a \<and> c e1 \<noteq> b"
      using chain_closed[of e2 e1 v] assms by blast
    then show ?thesis using 4 by (auto simp: swap_def)
  qed
qed

lemma swap_proper:
  assumes "proper_colouring_on E' c k" "a < k" "b < k"
  shows "proper_colouring_on E' swap k"
proof (rule proper_colouring_onI)
  fix e assume "e \<in> E'"
  then show "swap e < k"
    using assms proper_colouring_onD(1) by (auto simp: swap_def)
next
  fix e1 e2 v
  assume "e1 \<in> E'" "e2 \<in> E'" "e1 \<noteq> e2" "v \<in> e1" "v \<in> e2"
  then show "swap e1 \<noteq> swap e2"
    by (rule swap_distinct)
qed

text \<open>After the swap, colour \<open>a\<close> is missing at \<open>y\<close>.\<close>

lemma swap_a_missing_at_y:
  assumes "e \<in> E'" "y \<in> e"
  shows "swap e \<noteq> a"
proof (cases "e \<in> chain")
  case True
  then have "c e = a"
    using chain_colour b_missing_at_y assms by blast
  then show ?thesis
    using True a_neq_b by (simp add: swap_def)
next
  case False
  obtain z where e_def: "e = {y, z}"
    using edge_endpoints[OF assms] .
  have "c e \<noteq> a"
  proof
    assume "c e = a"
    then have "e \<in> chain"
      using chainI[of 0 y z] reach_0 assms(1) e_def by simp
    then show False using False by contradiction
  qed
  then show ?thesis
    using False by (simp add: swap_def)
qed

text \<open>
  If \<open>x \<in> X\<close> is a vertex at which colour \<open>a\<close> is missing, then colour \<open>a\<close>
  is still missing at \<open>x\<close> after the swap.
\<close>

lemma swap_a_missing_at_X:
  assumes x: "x \<in> X" and a_missing: "\<And>e. e \<in> E' \<Longrightarrow> x \<in> e \<Longrightarrow> c e \<noteq> a"
    and e: "e \<in> E'" "x \<in> e"
  shows "swap e \<noteq> a"
proof (cases "e \<in> chain")
  case False
  then show ?thesis using a_missing e by (simp add: swap_def)
next
  case True
  have "c e \<noteq> a" using a_missing e .
  then have ce: "c e = b" using chain_colour True by blast
  obtain i u w where e_def: "e = {u, w}" "reach i u" "{u, w} \<in> E'" "c {u, w} = col i"
    using True by (rule chainE)
  have odd_i: "odd i"
    using e_def(1,4) ce col_eq_b_iff by simp
  have "reach (Suc i) w"
    using reach_Suc e_def(2-4) by blast
  then have "w \<in> Y"
    using odd_i reach_even_in_Y by simp
  then have "x = u"
    using e(2) e_def(1) x disjoint by auto
  from odd_i obtain j where "i = Suc j"
    by (cases i) auto
  then obtain u' where u': "reach j u'" "{u', u} \<in> E'" "c {u', u} = col j"
    using e_def(2) by (auto elim: reach_SucE)
  have "col j = a"
    using odd_i \<open>i = Suc j\<close> by (simp add: col_def)
  then have False
    using a_missing[OF u'(2)] u'(3) \<open>x = u\<close> by simp
  then show ?thesis ..
qed

end

subsection \<open>Proof of K\H{o}nig's theorem\<close>

context fin_bipartite_graph
begin

text \<open>
  Every set of edges of a finite bipartite graph in
  which each vertex meets at most \<open>k\<close> edges has a proper \<open>k\<close>-edge-colouring.
  Formulating the statement for subsets of \<^term>\<open>E\<close> enables induction on the
  edge set without leaving the locale. The argument, adding one edge at a time
  and recolouring along an alternating chain where necessary, follows the
  standard proof \<^cite>\<open>\<open>Proposition 5.3.1\<close> in diestel\<close>.
\<close>

lemma edge_colouring_subset:
  assumes "E' \<subseteq> E" "\<And>v. card (edges_at E' v) \<le> k"
  shows "\<exists>c. proper_colouring_on E' c k"
proof -
  have "finite E'"
    using assms(1) fin_edges finite_subset by blast
  then show ?thesis
    using assms
  proof (induction E' rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert e E')
    have finE: "finite (edges_at E' v)" for v
      using insert.hyps(1) by blast
    have "card (edges_at E' v) \<le> k" for v
      using insert.prems(2)[of v] card_mono[OF _ edges_at_mono[of E' "insert e E'" v]]
        insert.hyps(1) by fastforce
    then obtain c where c: "proper_colouring_on E' c k"
      using insert.IH insert.prems(1) by blast
    have "e \<in> E" using insert.prems(1) by blast
    then obtain x y where xy: "x \<in> X" "y \<in> Y" "e = {x, y}"
      using edge_betw_indiv by blast
    have e_notin: "e \<notin> edges_at E' v" for v
      using insert.hyps(2) unfolding edges_at_def by blast
    have card_lt: "card (edges_at E' v) < k" if "v \<in> e" for v
      using insert.prems(2)[of v] edges_at_insert_in[OF that, of E'] finE e_notin by simp
    obtain \<alpha> where \<alpha>: "\<alpha> < k" "\<alpha> \<notin> c ` edges_at E' x"
      using missing_colour[OF finE card_lt] xy(3) by blast
    obtain \<beta> where \<beta>: "\<beta> < k" "\<beta> \<notin> c ` edges_at E' y"
      using missing_colour[OF finE card_lt] xy(3) by blast
    have \<alpha>_at_x: "c e' \<noteq> \<alpha>" if "e' \<in> E'" "x \<in> e'" for e'
      using \<alpha>(2) that unfolding edges_at_def by blast
    have \<beta>_at_y: "c e' \<noteq> \<beta>" if "e' \<in> E'" "y \<in> e'" for e'
      using \<beta>(2) that unfolding edges_at_def by blast
    have meets: "x \<in> e' \<or> y \<in> e'" if "e' \<inter> e \<noteq> {}" for e'
      using that xy(3) by blast
    show ?case
    proof (cases "\<alpha> \<in> c ` edges_at E' y")
      case False
      \<comment> \<open>Colour \<open>\<alpha>\<close> is missing at both endpoints: colour the new edge with \<open>\<alpha>\<close>.\<close>
      then have "c e' \<noteq> \<alpha>" if "e' \<in> E'" "y \<in> e'" for e'
        using that unfolding edges_at_def by blast
      then have "proper_colouring_on (insert e E') (c(e := \<alpha>)) k"
        using proper_colouring_on_insert[OF c insert.hyps(2) \<alpha>(1)] \<alpha>_at_x meets by blast
      then show ?thesis by blast
    next
      case True
      \<comment> \<open>Otherwise swap \<open>\<alpha>\<close> and \<open>\<beta>\<close> along the alternating chain starting at \<open>y\<close>.\<close>
      then have "\<alpha> \<noteq> \<beta>" using \<beta>(2) by blast
      interpret S: alternating_chain E' c \<alpha> \<beta> y X Y
      proof
        show "c e1 \<noteq> c e2" if "e1 \<in> E'" "e2 \<in> E'" "e1 \<noteq> e2" "v \<in> e1" "v \<in> e2" for e1 e2 v
          using proper_colouring_onD(2)[OF c] that .
        show "\<exists>p q. e' = {p, q} \<and> p \<in> X \<and> q \<in> Y" if "e' \<in> E'" for e'
          using that insert.prems(1) edge_betw_indiv by (metis insert_subset subsetD)
        show "X \<inter> Y = {}" by (rule part_intersect_empty)
        show "y \<in> Y" by (rule xy(2))
        show "\<alpha> \<noteq> \<beta>" by fact
        show "c e' \<noteq> \<beta>" if "e' \<in> E'" "y \<in> e'" for e'
          using \<beta>_at_y that .
      qed
      have swap: "proper_colouring_on E' S.swap k"
        using S.swap_proper[OF c \<alpha>(1) \<beta>(1)] .
      have "S.swap e' \<noteq> \<alpha>" if "e' \<in> E'" "e' \<inter> e \<noteq> {}" for e'
        using meets[OF that(2)] S.swap_a_missing_at_y[OF that(1)]
          S.swap_a_missing_at_X[OF xy(1) \<alpha>_at_x that(1)] by blast
      then have "proper_colouring_on (insert e E') (S.swap(e := \<alpha>)) k"
        using proper_colouring_on_insert[OF swap insert.hyps(2) \<alpha>(1)] by blast
      then show ?thesis by blast
    qed
  qed
qed

end

text \<open>Proper edge colourings and the chromatic index of a graph.\<close>

context graph_system
begin

abbreviation proper_edge_colouring :: "('a edge \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "proper_edge_colouring c k \<equiv> proper_colouring_on E c k"

definition edge_colourable :: "nat \<Rightarrow> bool" where
  "edge_colourable k \<longleftrightarrow> (\<exists>c. proper_edge_colouring c k)"

definition chromatic_index :: nat where
  "chromatic_index = (LEAST k. edge_colourable k)"

lemma edges_at_E: "edges_at E v = incident_edges v"
  unfolding edges_at_def incident_edges_def vincident_def by simp

end

context fin_sgraph
begin

lemma degree_le_max_degree: "degree v \<le> max_degree"
proof (cases "v \<in> V")
  case True
  have "finite {degree v | v. v \<in> V}"
    using finV by simp
  then show ?thesis
    unfolding max_degree_def using True Max_ge by blast
next
  case False
  then show ?thesis
    using incident_edges_empty[OF False] by simp
qed

lemma max_degree_attained:
  assumes "V \<noteq> {}"
  obtains v where "v \<in> V" "degree v = max_degree"
proof -
  have "finite {degree v | v. v \<in> V}" "{degree v | v. v \<in> V} \<noteq> {}"
    using finV assms by auto
  then have "max_degree \<in> {degree v | v. v \<in> V}"
    unfolding max_degree_def by (rule Max_in)
  then show ?thesis using that by force
qed

text \<open>The trivial lower bound: every proper edge colouring uses at least \<open>\<Delta>\<close> colours.\<close>

lemma max_degree_le_colours:
  assumes "V \<noteq> {}" "proper_edge_colouring c k"
  shows "max_degree \<le> k"
proof -
  obtain v where "v \<in> V" "degree v = max_degree"
    using max_degree_attained[OF assms(1)] .
  then show ?thesis
    using proper_colouring_on_card_edges_at[OF assms(2), of v] edges_at_E by simp
qed

lemma max_degree_le_chromatic_index:
  assumes "V \<noteq> {}" "edge_colourable k"
  shows "max_degree \<le> k"
  using assms max_degree_le_colours unfolding edge_colourable_def by blast

end

text \<open>A finite bipartite graph is in particular a finite simple graph.\<close>

sublocale fin_bipartite_graph \<subseteq> fin_sgraph
  by unfold_locales

context fin_bipartite_graph
begin

text \<open>
  Every finite bipartite graph has a proper edge colouring with \<open>\<Delta>\<close> colours.
\<close>

theorem max_degree_edge_colouring: "\<exists>c. proper_edge_colouring c max_degree"
proof (rule edge_colouring_subset)
  show "E \<subseteq> E" ..
  show "card (edges_at E v) \<le> max_degree" for v
    using degree_le_max_degree[of v] edges_at_E by simp
qed

corollary edge_colourable_max_degree: "edge_colourable max_degree"
  using max_degree_edge_colouring unfolding edge_colourable_def .

lemma vertices_nonempty: "V \<noteq> {}"
  using X_not_empty partitions_ss by blast

text \<open>
  \textbf{K\H{o}nig's edge colouring theorem} \<^cite>\<open>koenig1916\<close>: the chromatic
  index of a finite bipartite graph equals its maximum degree.
\<close>

theorem koenig_edge_colouring: "chromatic_index = max_degree"
  unfolding chromatic_index_def
proof (rule Least_equality)
  show "edge_colourable max_degree"
    by (rule edge_colourable_max_degree)
  show "max_degree \<le> k" if "edge_colourable k" for k
    using max_degree_le_chromatic_index[OF vertices_nonempty that] .
qed

end

section \<open>Regular Bipartite Graphs Decompose into Perfect Matchings\<close>

context graph_system
begin

text \<open>
  A `matching' is a set of edges of the graph, no two of which share a vertex.
\<close>

definition matching :: "'a edge set \<Rightarrow> bool" where
  "matching M \<longleftrightarrow> M \<subseteq> E \<and> (\<forall>e1\<in>M. \<forall>e2\<in>M. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {})"

text \<open>
  A matching is `perfect' if it covers every vertex of the graph, i.e.\ every
  vertex lies on exactly one edge of the matching.
\<close>

definition perfect_matching :: "'a edge set \<Rightarrow> bool" where
  "perfect_matching M \<longleftrightarrow> matching M \<and> (\<forall>v\<in>V. \<exists>e\<in>M. v \<in> e)"

text \<open>The colour classes of a proper edge colouring are matchings.\<close>

lemma colour_class_matching:
  assumes "proper_edge_colouring c k"
  shows "matching {e \<in> E. c e = i}"
  using proper_colouring_onD(2)[OF assms] unfolding matching_def by blast

text \<open>
  A family \<open>M 0, \<dots>, M (k - 1)\<close> of edge sets is a `decomposition of the graph into
  \<open>k\<close> perfect matchings' if the edge set is the disjoint union over all \<open>M i\<close>,
  and each \<open>M i\<close> is a perfect matching.
\<close>

definition perfect_matching_decomposition :: "(nat \<Rightarrow> 'a edge set) \<Rightarrow> nat \<Rightarrow> bool" where
  "perfect_matching_decomposition M k \<longleftrightarrow>
     (\<Union>i<k. M i) = E \<and> disjoint_family_on M {..<k} \<and> (\<forall>i<k. perfect_matching (M i))"

end

context fin_bipartite_graph
begin

text \<open>
  A \<open>k\<close>-regular bipartite graph has a proper \<open>k\<close>-edge-colouring in which every
  colour class is a perfect matching.
\<close>

theorem regular_colour_classes_perfect_matchings:
  assumes regular: "\<And>v. v \<in> V \<Longrightarrow> degree v = k"
  shows "\<exists>c. proper_edge_colouring c k \<and> (\<forall>i<k. perfect_matching {e \<in> E. c e = i})"
proof -
  have "max_degree = k"
    using max_degree_attained[OF vertices_nonempty] regular by metis
  then obtain c where c: "proper_edge_colouring c k"
    using max_degree_edge_colouring by blast
  have "perfect_matching {e \<in> E. c e = i}" if "i < k" for i
    unfolding perfect_matching_def
  proof (intro conjI ballI)
    show "matching {e \<in> E. c e = i}"
      using colour_class_matching[OF c] .
  next
    fix v assume v: "v \<in> V"
    have inj: "inj_on c (edges_at E v)"
      using proper_colouring_on_inj_on_edges_at[OF c] .
    have sub: "c ` edges_at E v \<subseteq> {0..<k}"
      using proper_colouring_onD(1)[OF c] unfolding edges_at_def by auto
    have "card (c ` edges_at E v) = k"
      using card_image[OF inj] regular[OF v] edges_at_E by simp
    then have "c ` edges_at E v = {0..<k}"
      using sub by (intro card_subset_eq) auto
    then have "i \<in> c ` edges_at E v"
      using that by simp
    then show "\<exists>e\<in>{e \<in> E. c e = i}. v \<in> e"
      unfolding edges_at_def by blast
  qed
  then show ?thesis using c by blast
qed

corollary regular_has_perfect_matching:
  assumes "\<And>v. v \<in> V \<Longrightarrow> degree v = k" "k > 0"
  shows "\<exists>M. perfect_matching M"
  using regular_colour_classes_perfect_matchings[OF assms(1)] assms(2) by blast

text \<open>
  K\H{o}nig's original application: the edge set of a \<open>k\<close>-regular bipartite
  graph is the disjoint union of \<open>k\<close> perfect matchings, namely the colour
  classes of the colouring above.
\<close>

theorem regular_decomposes_into_perfect_matchings:
  assumes regular: "\<And>v. v \<in> V \<Longrightarrow> degree v = k"
  shows "\<exists>M. perfect_matching_decomposition M k"
proof -
  obtain c where c: "proper_edge_colouring c k"
    and pm: "\<forall>i<k. perfect_matching {e \<in> E. c e = i}"
    using regular_colour_classes_perfect_matchings[OF regular] by blast
  let ?M = "\<lambda>i. {e \<in> E. c e = i}"
  have "(\<Union>i<k. ?M i) = E"
    using proper_colouring_onD(1)[OF c] by auto
  moreover have "disjoint_family_on ?M {..<k}"
    unfolding disjoint_family_on_def by auto
  ultimately show ?thesis
    using pm unfolding perfect_matching_decomposition_def by blast
qed

end

end
