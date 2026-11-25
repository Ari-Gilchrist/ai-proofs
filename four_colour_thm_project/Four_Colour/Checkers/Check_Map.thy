(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
theory Check_Map
  imports Four_Colour_Presentations.PresentBase
begin

definition tab_fun :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "tab_fun b h = (let t = map h [0..<b] in (\<lambda>x. if x < b then t ! x else x))"

lemma tab_fun_eq:
  assumes "\<And>x. b \<le> x \<Longrightarrow> h x = x"
  shows "tab_fun b h = h"
  using assms by (auto simp: tab_fun_def fun_eq_iff)

definition tab_map :: "nat hypermap \<Rightarrow> nat hypermap" where
  "tab_map G = (let b = Suc (Max (darts G)) in
    \<lparr>darts = darts G, edge = tab_fun b (edge G),
     node = tab_fun b (node G), face = tab_fun b (face G)\<rparr>)"

lemma tab_map_eq:
  assumes "hypermap G"
  shows "tab_map G = G"
proof -
  interpret H: hypermap G by (rule assms)
  have out: "x \<notin> darts G" if "Suc (Max (darts G)) \<le> x" for x
    using Max_ge[OF H.finite_darts, of x] that by auto
  have e: "tab_fun (Suc (Max (darts G))) (edge G) = edge G"
    by (rule tab_fun_eq) (simp add: out)
  have nd: "tab_fun (Suc (Max (darts G))) (node G) = node G"
    by (rule tab_fun_eq) (simp add: out)
  have f: "tab_fun (Suc (Max (darts G))) (face G) = face G"
    by (rule tab_fun_eq) (simp add: out)
  show ?thesis by (simp add: tab_map_def e nd f)
qed

context fperm
begin

lemma order_card_bound: "order f x \<le> Suc (card D)"
proof (cases "x \<in> D")
  case True
  have "card (cyc f x) \<le> card D" by (rule card_mono[OF fin cyc_subset[OF True]])
  then show ?thesis by (simp add: order_def)
qed (simp add: order_out)

lemma bounded_cyc:
  assumes b: "order f x \<le> b"
  shows "set (traject f x b) = cyc f x"
proof
  show "set (traject f x b) \<subseteq> cyc f x"
    by (auto simp: traject_def cyc_def fconnect_def)
  show "cyc f x \<subseteq> set (traject f x b)"
    using cyc_order[of x] b by (auto simp: traject_def)
qed

end

definition map_cyc :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat set" where
  "map_cyc G h x = set (traject h x (Suc (card (darts G))))"

definition map_order :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "map_order G h x = card (map_cyc G h x)"

lemma map_cyc_eq:
  assumes "fperm h (darts G)"
  shows "map_cyc G h x = cyc h x"
  unfolding map_cyc_def
  by (rule fperm.bounded_cyc[OF assms fperm.order_card_bound[OF assms]])

lemma map_order_eq:
  "fperm h (darts G) \<Longrightarrow> map_order G h x = order h x"
  by (simp add: map_order_def map_cyc_eq order_def)


lemma map_cyc_fun: "fperm h (darts G) \<Longrightarrow> map_cyc G h = cyc h"
  by (rule ext) (erule map_cyc_eq)

lemma map_order_fun: "fperm h (darts G) \<Longrightarrow> map_order G h = order h"
  by (rule ext) (erule map_order_eq)

definition map_A :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat hypermap" where
  "map_A G x0 = (let cc = node G x0 \<in> map_cyc G (face G) (edge G x0) in
    \<lparr>darts = darts G,
      edge = (\<lambda>x. if \<not> cc then edge G x
        else if x = x0 then edge G (node G (node G x0))
        else if x = node G (node G x0) then edge G x0 else edge G x),
      node = ecpA_node G x0,
      face = (\<lambda>x. if cc then face G x
        else if x = edge G x0 then node G x0
        else if face G x = node G x0 then face G (edge G x0) else face G x)\<rparr>)"

lemma map_A_eq: "hypermap G \<Longrightarrow> map_A G x = ecpA G x"
proof -
  assume h: "hypermap G"
  interpret H: hypermap G by (rule h)
  show ?thesis
    by (simp add: map_A_def ecpA_def ecpA_edge_def ecpA_face_def Let_def fun_eq_iff
        map_cyc_eq[OF H.F.fperm_axioms] cyc_def)
qed

fun map_step :: "cpstep \<Rightarrow> (nat hypermap \<times> nat) \<Rightarrow> nat hypermap \<times> nat" where
  "map_step (CpR k) (G, x) = (G, (node G ^^ (map_order G (node G) x - k)) x)"
| "map_step CpR' (G, x) = (G, node G x)"
| "map_step CpU (G, x) = (ecpU G x, ecpX G)"
| "map_step CpY (G, x) = (ecpN (ecpU G x) (ecpX G), ecpX (ecpU G x))"
| "map_step CpH (G, x) =
     (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)), ecpX (ecpN (ecpU G x) (ecpX G)))"
| "map_step CpK (G, x) =
     (ecpN G (node G x), face (ecpN G (node G x)) (edge (ecpN G (node G x)) (ecpX G)))"
| "map_step CpA (G, x) = (let A = map_A G x in
     (A, face A (edge A (face G (edge G x)))))"

lemma cpmap_Cons_step: "cpmap (s # cp) = map_step s (cpmap cp)"
proof -
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret H: hypermap G using hypermap_cpmap[of cp] c by simp
  show ?thesis by (cases s) (simp_all add: c map_order_eq[OF H.N.fperm_axioms] map_A_eq[OF H.hypermap_axioms] ecpA_ptr_def ecpA_def Let_def)
qed

fun cpmap_eval :: "cprog \<Rightarrow> nat hypermap \<times> nat" where
  "cpmap_eval [] = (cpmap0, 1)"
| "cpmap_eval (s # cp) = (case map_step s (cpmap_eval cp) of (G, x) \<Rightarrow> (tab_map G, x))"

lemma cpmap_eval_eq: "cpmap_eval cp = cpmap cp"
proof (induction cp)
  case Nil then show ?case by simp
next
  case (Cons s cp)
  have t: "tab_map (fst (cpmap (s # cp))) = fst (cpmap (s # cp))"
    by (rule tab_map_eq[OF hypermap_cpmap])
  show ?case
    using t by (simp only: cpmap_eval.simps Cons.IH cpmap_Cons_step[symmetric])
       (cases "cpmap (s # cp)", simp)
qed

lemma cpmap_code [code]: "cpmap cp = cpmap_eval cp"
  by (rule cpmap_eval_eq[symmetric])


declare traject_0[code] traject_Suc[code]

lemma map_face_perm: "hypermap G \<Longrightarrow> fperm (face G) (darts G)"
  by (simp add: fperm_def hypermap.finite_darts hypermap.face_perm)

lemma map_node_perm: "hypermap G \<Longrightarrow> fperm (node G) (darts G)"
  by (simp add: fperm_def hypermap.finite_darts hypermap.node_perm)

lemma cpring_of_code [code]:
  "cpring_of cp = (let G = cpG cp; x = cpx cp; y = node G (node G x) in
     rev (traject (node G) y (map_order G (node G) y)))"
  using map_order_eq[OF map_node_perm[OF hypermap_cpmap[of cp]]]
  by (simp add: cpring_of_def cpring_def orb_def Let_def)

definition map_band :: "nat hypermap \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "map_band G p x = list_ex (\<lambda>y. y \<in> map_cyc G (face G) x) p"

lemma map_band_eq:
  "hypermap G \<Longrightarrow> map_band G p x = fband G p x"
  by (simp add: map_band_def list_ex_iff map_cyc_eq[OF map_face_perm] fband_def cyc_def)

definition check_quiz :: "nat hypermap \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> quiz \<Rightarrow> bool" where
  "check_quiz G r u q = (let w = walkqz G u q in
    isQuizR q \<and> flatqz q = map (map_order G (face G)) w \<and>
    distinct (map (map_cyc G (face G)) w) \<and>
    list_all (\<lambda>x. map_band G w x = (\<not> map_band G r x)) (sorted_list_of_set (darts G)))"

lemma check_quiz_eq:
  assumes "hypermap G"
  shows "check_quiz G r u q = valid_quiz G r u q"
proof -
  interpret H: hypermap G by (rule assms)
  show ?thesis
    by (simp add: check_quiz_def valid_quiz_def fitqz_def simple_def kernel_def
        map_order_fun[OF H.F.fperm_axioms] map_cyc_fun[OF H.F.fperm_axioms]
        map_band_eq[OF assms] list_all_iff H.finite_darts Let_def)
qed

definition map_adj :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "map_adj G x y = (\<exists>z \<in> map_cyc G (face G) x. y \<in> map_cyc G (face G) (edge G z))"

lemma map_adj_eq:
  "hypermap G \<Longrightarrow> map_adj G x y = adj G x y"
  by (simp add: map_adj_def map_cyc_eq[OF map_face_perm] cyc_def adj_def rlink_def)

definition check_radius :: "nat hypermap \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_radius G r = (let ds = sorted_list_of_set (darts G);
      ks = filter (\<lambda>x. \<not> map_band G r x) ds in
    list_ex (\<lambda>x. list_all (\<lambda>y. list_ex (\<lambda>z. map_adj G y z \<and> map_adj G x z) ks) ks) ks)"

lemma check_radius_eq:
  assumes "hypermap G"
  shows "check_radius G r = radius2 G (kernel G r)"
proof -
  interpret H: hypermap G by (rule assms)
  have ad: "z \<in> darts G" if hyp: "y \<in> darts G" "adj G y z" for y z
  proof -
    obtain w where a: "fconnect (face G) y w" and b: "fconnect (face G) (edge G w) z"
      using hyp(2) by (auto simp: adj_def rlink_def)
    have w: "w \<in> darts G" using H.F.fconnect_in_D[OF a] hyp(1) by simp
    have "edge G w \<in> darts G" using w by simp
    then show ?thesis using H.F.fconnect_in_D[OF b] by simp
  qed
  show ?thesis
    using assms
    by (simp add: check_radius_def radius2_def at_radius2_def kernel_def Let_def
        list_ex_iff list_all_iff H.finite_darts map_band_eq map_adj_eq; blast intro: ad)
qed

definition check_embeddable :: "cprog \<Rightarrow> bool" where
  "check_embeddable cp = (let G = cpG cp; r = rev (cpring_of cp) in
    cubic_prog cp \<and> distinct (map (map_cyc G (face G)) r) \<and>
    list_all (\<lambda>x. map_order G (face G) x \<in> {3,4,5,6}) r \<and> check_radius G r)"

lemma check_embeddable_valid:
  assumes ck: "check_embeddable cp"
  shows "embeddable (cpG cp) (rev (cpring_of cp))"
proof -
  let ?G = "cpG cp" let ?r = "rev (cpring_of cp)"
  interpret H: hypermap ?G by (rule hypermap_cpmap)
  have c: "cubic_prog cp" and s: "simple ?G ?r"
    and a: "\<forall>x \<in> set ?r. good_ring_arity ?G x"
    and rad: "radius2 ?G (kernel ?G ?r)"
    using ck
    by (simp_all add: check_embeddable_def Let_def simple_def good_ring_arity_def
        map_cyc_fun[OF H.F.fperm_axioms] map_order_fun[OF H.F.fperm_axioms]
        check_radius_eq[OF H.hypermap_axioms] list_all_iff)
  have rD: "set ?r \<subseteq> darts ?G"
    using H.ringD_gen[OF cpx_in[of cp]] by (simp add: cpring_of_def)
  show ?thesis
    using geo_cpmap[OF c] H.ucycle_rev_cpring[of "cpx cp"] s a rad rD H.hypermap_axioms
    by (simp add: embeddable_def scycle_planar_bridgeless_plain_quasicubic_connected_def
        ucycle_plain_quasicubic_connected_def ucycle_plain_quasicubic_def
        plain_quasicubic_def geo_def cpring_of_def)
qed


definition check_cfquiz :: "config \<Rightarrow> bool" where
  "check_cfquiz cf = (let q = cfquiz cf; cp = cfprog cf; G = cpG cp; r = cfring cf in
    if isQuizR q then check_embeddable cp \<and>
       list_ex (\<lambda>u. check_quiz G r u q) (sorted_list_of_set (darts G))
    else True)"

lemma check_cfquiz_valid:
  assumes ck: "check_cfquiz cf"
  shows "cfquiz_correct cf"
proof (unfold cfquiz_correct_def, intro impI)
  assume qr: "isQuizR (cfquiz cf)"
  have emb: "check_embeddable (cfprog cf)"
    and v: "list_ex (\<lambda>u. check_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf))
      (sorted_list_of_set (darts (cpG (cfprog cf))))"
    using ck qr by (simp_all add: check_cfquiz_def Let_def)
  have e: "embeddable (cpG (cfprog cf)) (cfring cf)"
    using check_embeddable_valid[OF emb] by (simp add: cfring_def)
  have "\<exists>u. valid_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf) \<and>
      u \<in> darts (cpG (cfprog cf))"
    using v by (auto simp: list_ex_iff check_quiz_eq[OF hypermap_cpmap]
        hypermap.finite_darts[OF hypermap_cpmap])
  then show "embeddable (cpG (cfprog cf)) (cfring cf) \<and>
      (\<exists>u. valid_quiz (cpG (cfprog cf)) (cfring cf) u (cfquiz cf) \<and>
        u \<in> darts (cpG (cfprog cf)))" using e by blast
qed


definition face_cycles :: "nat hypermap \<Rightarrow> nat \<Rightarrow> nat set" where
  "face_cycles G = (let b = Suc (Max (darts G));
      t = map (map_cyc G (face G)) [0..<b] in
    (\<lambda>x. if x < b then t ! x else {x}))"

lemma face_cycles_eq:
  assumes h: "hypermap G"
  shows "face_cycles G = map_cyc G (face G)"
proof (rule ext)
  interpret H: hypermap G by (rule h)
  fix x
  have out: "x \<notin> darts G" if "Suc (Max (darts G)) \<le> x"
    using Max_ge[OF H.finite_darts, of x] that by auto
  show "face_cycles G x = map_cyc G (face G) x"
    by (simp add: face_cycles_def Let_def map_cyc_fun[OF H.F.fperm_axioms] H.F.cyc_out out
        del: upt_Suc)
qed

definition band_with :: "(nat \<Rightarrow> nat set) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "band_with C p x = list_ex (\<lambda>y. y \<in> C x) p"

definition adj_with :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "adj_with G C x y = (\<exists>z \<in> C x. y \<in> C (edge G z))"

definition radius_with :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat list \<Rightarrow> bool" where
  "radius_with G C r = (let ds = sorted_list_of_set (darts G);
      ks = filter (\<lambda>x. \<not> band_with C r x) ds in
    list_ex (\<lambda>x. list_all (\<lambda>y. list_ex (\<lambda>z. adj_with G C y z \<and> adj_with G C x z) ks) ks) ks)"

definition quiz_with :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> quiz \<Rightarrow> bool" where
  "quiz_with G C r u q = (let w = walkqz G u q in
    isQuizR q \<and> flatqz q = map (\<lambda>x. card (C x)) w \<and> distinct (map C w) \<and>
    list_all (\<lambda>x. band_with C w x = (\<not> band_with C r x)) (sorted_list_of_set (darts G)))"

definition emb_with :: "nat hypermap \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat list \<Rightarrow> bool" where
  "emb_with G C r = (distinct (map C r) \<and>
    list_all (\<lambda>x. card (C x) \<in> {3,4,5,6}) r \<and> radius_with G C r)"

lemma map_order_lambda: "map_order G h = (\<lambda>x. card (map_cyc G h x))"
  by (rule ext) (simp add: map_order_def)

lemma quiz_with_eq:
  "quiz_with G (map_cyc G (face G)) r u q = check_quiz G r u q"
  by (simp add: quiz_with_def check_quiz_def band_with_def map_band_def map_order_lambda)

lemma radius_with_eq:
  "radius_with G (map_cyc G (face G)) r = check_radius G r"
  by (simp add: radius_with_def check_radius_def band_with_def map_band_def adj_with_def map_adj_def)

lemma check_cfquiz_cached [code]:
  "check_cfquiz cf = (let q = cfquiz cf; cp = cfprog cf; G = cpG cp; r = cfring cf;
      C = face_cycles G in
    if isQuizR q then cubic_prog cp \<and> emb_with G C r \<and>
      list_ex (\<lambda>u. quiz_with G C r u q) (sorted_list_of_set (darts G))
    else True)"
  by (simp add: check_cfquiz_def Let_def face_cycles_eq[OF hypermap_cpmap]
      quiz_with_eq emb_with_def radius_with_eq check_embeddable_def cfring_def map_order_lambda)

end
