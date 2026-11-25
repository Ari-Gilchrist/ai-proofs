(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Cfcolor.thy
    Colourings of configuration maps, computed from construction programs.
    Ported from G. Gonthier's Coq development (cfcolor.v), with the remaining
    trace lemmas of color.v.
*)
theory Cfcolor
  imports Four_Colour_Maps.Cfmap_prog Four_Colour_Maps.Ctree Four_Colour_Maps.Kempe
begin

section \<open>More trace lemmas (color.v)\<close>

lemma edge_rot_self: "c \<noteq> Color0 \<Longrightarrow> permc (edge_rot c) c = Color1"
  by (cases c) simp_all

lemma permc_fix1: "permc g Color1 = Color1 \<Longrightarrow> g = Eperm123 \<or> g = Eperm132"
  by (cases g) simp_all

lemma permc_132_1 [simp]: "permc Eperm123 c = c" by simp

lemma even_tail_132:
  "even_tail t \<Longrightarrow> even_tail (permt Eperm132 t) \<Longrightarrow> permt Eperm132 t = t"
proof (induction t)
  case (Cons c t)
  then show ?case by (cases c) simp_all
qed simp

lemma etail_perm:
  assumes "proper_trace et"
  shows "\<exists>g. permt g et = Color1 # etail et"
proof -
  obtain c et' where et: "et = c # et'" and c: "c \<noteq> Color0"
    using assms by (cases et) (auto simp: proper_trace_def head_color_def)
  define h where "h = etrace_perm et"
  have h1: "permc h Color1 = Color1" by (simp add: h_def etrace_perm_def)
  obtain g where g: "permt g et = permt h (permt (edge_rot c) et)"
    using compose_permt by blast
  have "permt h (permt (edge_rot c) et) = Color1 # etail et"
    using et c h1 assms by (simp add: etail_def ttail_def h_def edge_rot_self)
  then have "permt g et = Color1 # etail et" using g by simp
  then show ?thesis by blast
qed

lemma etail_unique:
  assumes g1: "permt g1 et = Color1 # t1" and g2: "permt g2 et = Color1 # t2"
    and e1: "even_tail t1" and e2: "even_tail t2"
  shows "t1 = t2"
proof -
  obtain g where g: "permt g (permt g1 et) = permt g2 et"
  proof -
    obtain g where "permt g (permt g1 et) = permt g2 (permt (inv_eperm g1) (permt g1 et))"
      using compose_permt by blast
    moreover have "permt (inv_eperm g1) (permt g1 et) = et"
      by (induction et) simp_all
    ultimately show ?thesis using that by simp
  qed
  then have gg: "permc g Color1 = Color1" and gt: "permt g t1 = t2" using g1 g2 by simp_all
  consider "g = Eperm123" | "g = Eperm132" using permc_fix1[OF gg] by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis using gt by simp
  next
    case 2 then show ?thesis using gt e1 e2 even_tail_132 by metis
  qed
qed

lemma etail_permt: "etail (permt g et) = etail et"
proof (cases "proper_trace et")
  case False
  then show ?thesis by (simp add: etail_def ttail_def)
next
  case True
  have pg: "proper_trace (permt g et)" using True by simp
  obtain h where h: "permt h (permt g et) = Color1 # etail (permt g et)"
    using etail_perm[OF pg] by blast
  obtain h' where h': "permt h' et = permt h (permt g et)" using compose_permt by blast
  obtain h'' where h'': "permt h'' et = Color1 # etail et" using etail_perm[OF True] by blast
  show ?thesis using etail_unique[OF h'[unfolded h] h'' even_etail even_etail] .
qed

lemma trace_rot: "trace (rot n lc) = rot n (trace lc)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "length lc \<le> n")
    case True
    then show ?thesis by (simp add: rot_oversize)
  next
    case False
    have "rot (Suc n) lc = rot 1 (rot n lc)" using False rot_add[of n 1 lc] by simp
    moreover have "rot (Suc n) (trace lc) = rot 1 (rot n (trace lc))"
      using False rot_add[of n 1 "trace lc"] by simp
    ultimately show ?thesis using Suc trace_rot1 by simp
  qed
qed

lemma nth_pairmap: "i < length l \<Longrightarrow> pairmap f x l ! i = f ((x # l) ! i) (l ! i)"
proof (induction l arbitrary: x i)
  case (Cons y l)
  then show ?case by (cases i) simp_all
qed simp

lemma trace_no0:
  assumes "\<forall>i < length lc. lc ! i \<noteq> lc ! (Suc i mod length lc)"
  shows "Color0 \<notin> set (trace lc)"
proof (cases lc)
  case Nil
  then show ?thesis by (simp add: trace_def)
next
  case (Cons c l)
  define L where "L = c # l @ [c]"
  have tr: "trace lc = pairmap addc c (l @ [c])" using Cons by (simp add: trace_Cons)
  have Lnth: "L ! i = lc ! (i mod length lc)" if "i \<le> length lc" for i
  proof (cases "i = length lc")
    case True
    then show ?thesis using Cons by (simp add: L_def nth_append)
  next
    case False
    then have "i < length lc" using that by simp
    then show ?thesis using Cons by (cases i) (simp_all add: L_def nth_append)
  qed
  show ?thesis
  proof
    assume "Color0 \<in> set (trace lc)"
    then obtain i where i: "i < length (l @ [c])" "pairmap addc c (l @ [c]) ! i = Color0"
      unfolding tr by (metis in_set_conv_nth length_pairmap)
    have "(c # l @ [c]) ! i +c (l @ [c]) ! i = Color0" using i(2) nth_pairmap[OF i(1), of "(+c)" c] by simp
    then have eq: "L ! i = L ! Suc i" by (simp add: L_def addc_eq0)
    have il: "i < length lc" using i Cons by simp
    have "lc ! i = lc ! (Suc i mod length lc)"
      using eq Lnth[of i] Lnth[of "Suc i"] il by simp
    then show False using assms il by blast
  qed
qed

section \<open>Ring traces of colourings\<close>

context hypermap
begin

lemma cycle_inv_cpring: "cycle (frel (inv n)) (cpring G x0)"
proof -
  interpret IN: fperm "inv n" D by (rule inv_node_fperm)
  show ?thesis unfolding cpring_inv by (rule IN.cycle_orb)
qed

lemma memc0_trace_cpring:
  assumes col: "coloring G k" and x0: "x0 \<in> D"
  shows "Color0 \<notin> set (trace (map k (cpring G x0)))"
proof (rule trace_no0, intro allI impI)
  fix i assume i: "i < length (map k (cpring G x0))"
  define r where "r = cpring G x0"
  have i': "i < length r" using i by (simp add: r_def)
  have nxt: "r ! (Suc i mod length r) = inv n (r ! i)"
    using cycle_inv_cpring[of x0] i' by (simp add: cycle_nth r_def)
  have rD: "r ! i \<in> D" using ringD_gen[OF x0] i' nth_mem unfolding r_def by blast
  have "k (inv n (r ! i)) \<noteq> k (r ! i)"
  proof -
    have "inv n (r ! i) = f (e (r ! i))" by (rule inv_node_apply)
    moreover have "k (f (e (r ! i))) = k (e (r ! i))" using col rD by (simp add: coloring_def)
    moreover have "k (e (r ! i)) \<noteq> k (r ! i)" using col rD by (simp add: coloring_def)
    ultimately show ?thesis by simp
  qed
  moreover have "Suc i mod length r < length r" using i' by (intro mod_less_divisor) linarith
  ultimately show "map k (cpring G x0) ! i \<noteq> map k (cpring G x0) ! (Suc i mod length (map k (cpring G x0)))"
    using nxt i' by (simp add: r_def)
qed

lemma coloring_proper_cpring:
  assumes col: "coloring G k" and x0: "x0 \<in> D"
  shows "proper_cpring G x0"
proof (rule ccontr)
  assume "\<not> proper_cpring G x0"
  then have "length (cpring G x0) = 1" using size_proper_cpring cpring_ne[of x0]
    by (cases "cpring G x0") auto
  then obtain c where "map k (cpring G x0) = [c]" by (cases "cpring G x0") auto
  then have "Color0 \<in> set (trace (map k (cpring G x0)))"
    by (simp add: trace_def ptrace_def ctrace_def)
  then show False using memc0_trace_cpring[OF col x0] by simp
qed

lemma trace_cpring_eq:
  assumes col: "coloring G k" and x0: "x0 \<in> D"
  shows "trace (map k (cpring G x0)) =
         (k (n x0) +c k x0) # (k x0 +c k (f (e x0))) # ptrace (map k (drop 2 (cpring G x0) @ [n x0]))"
proof -
  have pr: "proper_cpring G x0" by (rule coloring_proper_cpring[OF col x0])
  obtain rest where r: "cpring G x0 = n x0 # x0 # rest"
    using head_proper_cpring[OF pr] by blast
  have "trace (map k (cpring G x0)) = urtrace (rot 1 (map k (cpring G x0)))"
    by (rule urtrace_trace[symmetric])
  also have "rot 1 (map k (cpring G x0)) = k x0 # map k rest @ [k (n x0)]"
    unfolding r by (simp add: rot_def)
  also have "urtrace (k x0 # map k rest @ [k (n x0)]) =
             (k (n x0) +c k x0) # pairmap addc (k x0) (map k rest @ [k (n x0)])"
    by (simp add: urtrace_def)
  finally have t: "trace (map k (cpring G x0)) =
             (k (n x0) +c k x0) # pairmap addc (k x0) (map k rest @ [k (n x0)])" .
  show ?thesis
  proof (cases rest)
    case Nil
    have "\<not> long_cpring G x0" using r Nil size_long_cpring by simp
    then have "f (e x0) = n x0" by (simp add: long_cpring_def)
    then show ?thesis using t Nil r by (simp add: ptrace_def)
  next
    case (Cons z p)
    have "long_cpring G x0" using r Cons size_long_cpring by simp
    then have hl: "cpring G x0 = n x0 # x0 # f (e x0) # drop 3 (cpring G x0)" by (rule head_long_cpring)
    have "z = f (e x0)" using hl unfolding r Cons by simp
    then show ?thesis using t Cons r by (simp add: ptrace_def)
  qed
qed

lemma proper_trace_cpring:
  assumes col: "coloring G k" and x0: "x0 \<in> D"
  shows "proper_trace (tl (trace (map k (cpring G x0))))"
  using memc0_trace_cpring[OF col x0] trace_cpring_eq[OF col x0]
  by (simp add: proper_trace_def head_color_def eq_commute[of Color0])

end

section \<open>The colouring procedure\<close>

definition cpbranch :: "colseq \<Rightarrow> ctree" where
  "cpbranch et = ctree_of_ttail (etail (tl et))"


fun cpcolor1 :: "cpstep \<Rightarrow> (colseq \<Rightarrow> ctree) \<Rightarrow> colseq \<Rightarrow> ctree" where
  "cpcolor1 (CpR k) f et = f (rot k et)"
| "cpcolor1 CpR' f et = (if length et \<le> 1 then CtreeEmpty else f (rotr1 et))"
| "cpcolor1 CpU f et = ctree_union (f (Color1 # Color1 # et))
                        (ctree_union (f (Color2 # Color2 # et)) (f (Color3 # Color3 # et)))"
| "cpcolor1 CpK f (e1 # e2 # et) = (if e1 = e2 then CtreeEmpty else f ((e1 +c e2) # et))"
| "cpcolor1 CpY f (e1 # et) = ctree_union (f (permc Eperm231 e1 # permc Eperm312 e1 # et))
                                          (f (permc Eperm312 e1 # permc Eperm231 e1 # et))"
| "cpcolor1 CpH f (e1 # e2 # et) =
     (if e1 = e2 then ctree_union (f (permc Eperm231 e1 # permc Eperm231 e1 # et))
                                  (f (permc Eperm312 e1 # permc Eperm312 e1 # et))
      else f (e2 # e1 # et))"
| "cpcolor1 CpA f (e1 # e2 # et) = (if e1 = e2 then f (if et = [] then e1 # e2 # et else et) else CtreeEmpty)"
| "cpcolor1 _ f _ = CtreeEmpty"

definition cpcol :: "cprog \<Rightarrow> colseq \<Rightarrow> ctree" where
  "cpcol cp = foldr cpcolor1 cp cpbranch"

text \<open>Gonthier's cpcolor0 adds symmetry reductions for the first steps; we use the plain
  fold (equal as a set of traces), and leave the optimisation for later.\<close>

definition cpcolor0 :: "cprog \<Rightarrow> ctree" where
  "cpcolor0 cp = cpcol cp [Color1, Color1]"

definition cpcolor :: "cprog \<Rightarrow> ctree" where
  "cpcolor cp = ctree_cons_rot (cpcolor0 (rev cp))"

section \<open>The colouring invariant\<close>

lemma rot_map: "rot n (map f l) = map f (rot n l)"
  by (simp add: rot_def drop_map take_map)

lemma tl_urtrace: "l \<noteq> [] \<Longrightarrow> tl (urtrace l) = ptrace l"
  by (cases l) (simp_all add: urtrace_def ptrace_def)

lemma tl_trace_ptrace: "tl (trace lc) = ptrace (rot 1 lc)"
proof (cases "lc = []")
  case True
  then show ?thesis by (simp add: trace_def ptrace_def rot_def)
next
  case False
  then have "rot 1 lc \<noteq> []" by (simp add: rot_def)
  then show ?thesis using urtrace_trace[of lc] tl_urtrace by metis
qed

lemma coloring_adj:
  assumes col: "coloring G k" and h: "hypermap G" and a: "adj G x y" and x: "x \<in> darts G"
  shows "k x \<noteq> k y"
proof -
  interpret hypermap G by (rule h)
  obtain z where z: "cface x z" "cface (e z) y" using a unfolding adj_def rlink_def by blast
  have zD: "z \<in> D" using F.fconnect_in_D[OF z(1)] x by simp
  have "k z = k x" using coloring_cface[OF col z(1) x] .
  moreover have "k y = k (e z)" using coloring_cface[OF col z(2)] zD by simp
  moreover have "k (e z) \<noteq> k z" using col zD by (simp add: coloring_def)
  ultimately show ?thesis by simp
qed

definition cp_tr0 :: "colseq \<Rightarrow> cprog \<Rightarrow> cprog \<Rightarrow> (nat \<Rightarrow> color) \<Rightarrow> bool" where
  "cp_tr0 et0 cp1 cp2 k0 \<longleftrightarrow> ttail et0 = eptrace (rot 1 (map k0 (cpring_of (rev cp1 @ cp2))))"

definition ext_ok :: "colseq \<Rightarrow> cprog \<Rightarrow> cprog \<Rightarrow> (nat \<Rightarrow> color) \<Rightarrow> bool" where
  "ext_ok et0 cp1 cp2 k \<longleftrightarrow> (\<exists>k0. coloring (cpG (rev cp1 @ cp2)) k0 \<and> cp_tr0 et0 cp1 cp2 k0 \<and>
                                     (\<forall>x \<in> darts (cpG cp2). k0 x = k x))"

definition cp_extcol :: "colseq \<Rightarrow> cprog \<Rightarrow> cprog \<Rightarrow> (colseq \<Rightarrow> ctree) \<Rightarrow> (nat \<Rightarrow> color) \<Rightarrow> bool" where
  "cp_extcol et0 cp1 cp2 f k \<longleftrightarrow>
     ctree_proper (cprsize (rev cp1 @ cp2) - 2) (f (trace (map k (cpring_of cp2)))) \<and>
     (ctree_mem (f (trace (map k (cpring_of cp2)))) (ttail et0) \<longleftrightarrow> ext_ok et0 cp1 cp2 k)"

lemma gcol_perm:
  assumes "coloring G k0" "ttail et0 = eptrace (rot 1 (map k0 r))"
  shows "coloring G (\<lambda>x. c +c permc h (k0 x)) \<and> ttail et0 = eptrace (rot 1 (map (\<lambda>x. c +c permc h (k0 x)) r))"
proof
  have inj: "inj (\<lambda>a. c +c permc h a)" by (rule injI) (simp add: addcI permc_inj)
  show "coloring G (\<lambda>x. c +c permc h (k0 x))"
    using assms(1) by (simp add: coloring_def addcI permc_inj)
  have "map (\<lambda>x. c +c permc h (k0 x)) r = map (addc c) (permt h (map k0 r))"
    by (simp add: permt_def)
  then have "eptrace (rot 1 (map (\<lambda>x. c +c permc h (k0 x)) r)) =
             etail (ptrace (map (addc c) (rot 1 (permt h (map k0 r)))))"
    by (simp only: eptrace_def rot_map)
  also have "\<dots> = etail (ptrace (rot 1 (permt h (map k0 r))))" by (simp only: ptrace_addc)
  also have "rot 1 (permt h (map k0 r)) = permt h (rot 1 (map k0 r))"
    by (simp only: permt_def rot_map)
  also have "etail (ptrace (permt h (rot 1 (map k0 r)))) = eptrace (rot 1 (map k0 r))"
    by (simp only: ptrace_permt etail_permt eptrace_def)
  finally have "eptrace (rot 1 (map (\<lambda>x. c +c permc h (k0 x)) r)) = eptrace (rot 1 (map k0 r))" .
  then show "ttail et0 = eptrace (rot 1 (map (\<lambda>x. c +c permc h (k0 x)) r))" using assms(2) by simp
qed

lemma gcol_cface:
  assumes col: "coloring (cpG (rev cp1 @ cp2)) k0" and x: "x \<in> darts (cpG cp2)"
    and y: "y \<in> darts (cpG cp2)" and xy: "fconnect (face (cpG cp2)) x y"
  shows "k0 x = k0 y"
proof -
  have "fconnect (face (cpG (rev cp1 @ cp2))) x y" by (rule sub_cface_injcp[OF x y xy])
  moreover have "x \<in> darts (cpG (rev cp1 @ cp2))" using darts_injcp x by blast
  ultimately show ?thesis
    using hypermap.coloring_cface[OF hypermap_cpmap col] by metis
qed

lemma gcol_adj:
  assumes col: "coloring (cpG (rev cp1 @ cp2)) k0" and x: "x \<in> darts (cpG cp2)"
    and y: "y \<in> darts (cpG cp2)" and xy: "adj (cpG cp2) x y"
  shows "k0 x \<noteq> k0 y"
proof -
  have "adj (cpG (rev cp1 @ cp2)) x y" by (rule sub_adj_injcp[OF x y xy])
  moreover have "x \<in> darts (cpG (rev cp1 @ cp2))" using darts_injcp x by blast
  ultimately show ?thesis using coloring_adj[OF col hypermap_cpmap] by blast
qed

lemma ring_in_darts: "set (cpring_of cp) \<subseteq> darts (cpG cp)"
  using hypermap.ringD_gen[OF hypermap_cpmap cpx_in] by (simp add: cpring_of_def)

lemma cpbranch_correct:
  assumes col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 [] cp2 cpbranch k"
proof -
  interpret H: hypermap "cpG cp2" by (rule hypermap_cpmap)
  define et where "et = trace (map k (cpring_of cp2))"
  have nz: "Color0 \<notin> set et" unfolding et_def cpring_of_def by (rule H.memc0_trace_cpring[OF col cpx_in])
  have pt: "proper_trace (tl et)" unfolding et_def cpring_of_def by (rule H.proper_trace_cpring[OF col cpx_in])
  have nz': "Color0 \<notin> set (etail (tl et))"
  proof -
    have "Color0 \<notin> set (tl et)" using nz by (cases et) auto
    then show ?thesis using pt memc0_ttail[of "tl et"] by (simp add: etail_def)
  qed
  have len: "length (etail (tl et)) = cprsize cp2 - 2"
  proof -
    obtain c t where t: "tl et = c # t" using pt by (cases "tl et") (auto simp: proper_trace_def head_color_def)
    have "length et = cprsize cp2" using size_ring_cpmap[of cp2] by (simp add: et_def)
    then show ?thesis using t pt by (cases et) (simp_all add: etail_def ttail_def)
  qed
  have tl_eq: "tl et = ptrace (rot 1 (map k (cpring_of cp2)))" unfolding et_def by (rule tl_trace_ptrace)
  have ext: "ext_ok et0 [] cp2 k \<longleftrightarrow> ttail et0 = etail (tl et)"
  proof
    assume "ext_ok et0 [] cp2 k"
    then obtain k0 where k0: "cp_tr0 et0 [] cp2 k0" "\<forall>x \<in> darts (cpG cp2). k0 x = k x"
      by (auto simp: ext_ok_def)
    have meq: "map k0 (cpring_of cp2) = map k (cpring_of cp2)" using k0(2) ring_in_darts by (auto intro!: map_cong)
    have "ttail et0 = eptrace (rot 1 (map k0 (cpring_of cp2)))" using k0(1) by (simp add: cp_tr0_def)
    then show "ttail et0 = etail (tl et)" unfolding meq tl_eq eptrace_def .
  next
    assume "ttail et0 = etail (tl et)"
    then have "cp_tr0 et0 [] cp2 k" using tl_eq by (simp add: cp_tr0_def eptrace_def)
    then show "ext_ok et0 [] cp2 k" using col by (auto simp: ext_ok_def)
  qed
  show ?thesis
    unfolding cp_extcol_def et_def[symmetric] cpbranch_def ext
    using ctree_of_ttail_proper[OF len] ctree_of_ttail_mem[OF nz'] by simp
qed

lemma cpcolor1R_correct:
  assumes IH: "\<And>k'. coloring (cpG (CpR m # cp2)) k' \<Longrightarrow> cp_extcol et0 cp1 (CpR m # cp2) f k'"
    and col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 (CpR m # cp1) cp2 (cpcolor1 (CpR m) f) k"
proof -
  obtain G x where c: "cpmap cp2 = (G, x)" by (cases "cpmap cp2")
  interpret H: hypermap G using hypermap_cpmap[of cp2] c by simp
  have m: "cpmap (CpR m # cp2) = (G, H.ecpR_ptr m x)" using cpmap_Cons_cases(1)[OF c] .
  have r: "cpring_of (CpR m # cp2) = rot m (cpring_of cp2)"
    using m c by (simp add: cpring_of_def H.cpring_ecpR)
  have col': "coloring (cpG (CpR m # cp2)) k" using col m c by simp
  have dd: "darts (cpG (CpR m # cp2)) = darts (cpG cp2)" using m c by simp
  have "trace (map k (cpring_of (CpR m # cp2))) = rot m (trace (map k (cpring_of cp2)))"
    using r by (simp add: rot_map[symmetric] trace_rot)
  then show ?thesis using IH[OF col'] dd by (simp add: cp_extcol_def ext_ok_def cp_tr0_def)
qed

lemma cpcolor1R'_correct:
  assumes IH: "\<And>k'. coloring (cpG (CpR' # cp2)) k' \<Longrightarrow> cp_extcol et0 cp1 (CpR' # cp2) f k'"
    and col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 (CpR' # cp1) cp2 (cpcolor1 CpR' f) k"
proof -
  obtain G x where c: "cpmap cp2 = (G, x)" by (cases "cpmap cp2")
  interpret H: hypermap G using hypermap_cpmap[of cp2] c by simp
  have xD: "x \<in> darts G" using cpx_in[of cp2] c by simp
  have m: "cpmap (CpR' # cp2) = (G, node G x)" using cpmap_Cons_cases(2)[OF c] .
  have "cpring G (node G x) = rot (order (node G) x - 1) (cpring G x)"
    using H.cpring_ecpR[of "order (node G) x - 1" x] H.ecpR'_eq[of x] by simp
  then have r: "cpring_of (CpR' # cp2) = rotr1 (cpring_of cp2)"
    using m c by (simp add: cpring_of_def rotr1_def H.length_cpring)
  have col': "coloring (cpG (CpR' # cp2)) k" using col m c by simp
  have dd: "darts (cpG (CpR' # cp2)) = darts (cpG cp2)" using m c by simp
  have pr: "proper_cpring G x" using H.coloring_proper_cpring[OF _ xD] col c by simp
  have L: "\<not> length (trace (map k (cpring_of cp2))) \<le> 1"
    using pr H.size_proper_cpring c by (simp add: cpring_of_def)
  have "trace (map k (cpring_of (CpR' # cp2))) = rotr1 (trace (map k (cpring_of cp2)))"
    using r by (simp add: rotr1_def rot_map[symmetric] trace_rot)
  then show ?thesis using IH[OF col'] dd L by (simp add: cp_extcol_def ext_ok_def cp_tr0_def)
qed

lemma addc_same_iff [simp]: "a +c e = a \<longleftrightarrow> e = Color0" "e +c a = a \<longleftrightarrow> e = Color0"
  "a = a +c e \<longleftrightarrow> e = Color0" "a = e +c a \<longleftrightarrow> e = Color0"
  by (cases a; cases e; simp)+

lemma trace_U: "trace (a # (e +c a) # a # l) = e # e # trace (a # l)"
proof -
  have "trace (a # (e +c a) # a # l) = pairmap addc a ((e +c a) # a # l @ [a])" by (simp add: trace_Cons)
  also have "\<dots> = (a +c (e +c a)) # ((e +c a) +c a) # pairmap addc a (l @ [a])" by simp
  also have "a +c (e +c a) = e" by (simp add: addcC[of e a])
  also have "(e +c a) +c a = e" by simp
  finally show ?thesis by (simp add: trace_Cons)
qed

lemma rev_Cons_app: "rev (s # cp1) @ cp2 = rev cp1 @ s # cp2" by simp

lemma cpcolor1U_correct:
  assumes IH: "\<And>k'. coloring (cpG (CpU # cp2)) k' \<Longrightarrow> cp_extcol et0 cp1 (CpU # cp2) f k'"
    and col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 (CpU # cp1) cp2 (cpcolor1 CpU f) k"
proof -
  obtain G x where c: "cpmap cp2 = (G, x)" by (cases "cpmap cp2")
  interpret E: ecp G x using hypermap_cpmap[of cp2] cpx_in[of cp2] c by (intro ecp_intro) simp_all
  have m: "cpmap (CpU # cp2) = (E.GU, E.X)" using cpmap_Cons_cases(3)[OF c E.ecp_axioms] .
  have colG: "coloring G k" using col c by simp
  define a where "a = k (E.n x)"
  define k' where "k' e u = (if u = E.X then e +c a else if u = E.Xe then a else k u)" for e u
  have k'D: "u \<in> E.D \<Longrightarrow> k' e u = k u" for e u by (simp add: k'_def)
  have col': "coloring E.GU (k' e)" if e: "e \<noteq> Color0" for e
    unfolding coloring_def
  proof (intro conjI ballI)
    fix u assume u: "u \<in> darts E.GU"
    then consider "u \<in> E.D" | "u = E.X" | "u = E.Xe" by auto
    then show "k' e (edge E.GU u) \<noteq> k' e u"
    proof cases
      case 1 then show ?thesis using colG by (simp add: k'_def coloring_def)
    next
      case 2 then show ?thesis using e by (simp add: k'_def)
    next
      case 3 then show ?thesis using e by (simp add: k'_def)
    qed
    show "k' e (face E.GU u) = k' e u"
    proof (cases "u \<in> E.D")
      case True
      have "k (E.f u) = k u" using colG True by (simp add: coloring_def)
      then show ?thesis using True by (cases "E.f u = E.n x") (simp_all add: k'_def a_def)
    next
      case False
      then have "u = E.X \<or> u = E.Xe" using u by auto
      then show ?thesis by (auto simp: k'_def a_def)
    qed
  qed
  define et where "et = trace (map k (cpring_of cp2))"
  obtain rest where r: "cpring G x = E.n x # rest" using E.head_cpring[of x] by blast
  have tr: "trace (map (k' e) (cpring_of (CpU # cp2))) = e # e # et" for e
  proof -
    have "map (k' e) (cpring_of (CpU # cp2)) = a # (e +c a) # map k (cpring G x)"
      using m E.cpring_GU E.ringD k'D by (auto simp: cpring_of_def k'_def intro!: map_cong)
    also have "\<dots> = a # (e +c a) # a # map k rest" using r by (simp add: a_def)
    finally show ?thesis using trace_U[of a e "map k rest"] r c by (simp add: et_def cpring_of_def a_def)
  qed
  have h: "cprsize (rev (CpU # cp1) @ cp2) = cprsize (rev cp1 @ CpU # cp2)" by simp
  have I: "cp_extcol et0 cp1 (CpU # cp2) f (k' e)" if "e \<noteq> Color0" for e
    using IH[of "k' e"] col'[OF that] m by simp
  note I1 = I[of Color1, simplified, unfolded cp_extcol_def tr]
  note I2 = I[of Color2, simplified, unfolded cp_extcol_def tr]
  note I3 = I[of Color3, simplified, unfolded cp_extcol_def tr]
  define hh where "hh = cprsize (rev cp1 @ CpU # cp2) - 2"
  have p1: "ctree_proper hh (f (Color1 # Color1 # et))" and p2: "ctree_proper hh (f (Color2 # Color2 # et))"
    and p3: "ctree_proper hh (f (Color3 # Color3 # et))" using I1 I2 I3 by (simp_all add: hh_def)
  have ext: "ext_ok et0 (CpU # cp1) cp2 k \<longleftrightarrow>
             ext_ok et0 cp1 (CpU # cp2) (k' Color1) \<or> ext_ok et0 cp1 (CpU # cp2) (k' Color2) \<or>
             ext_ok et0 cp1 (CpU # cp2) (k' Color3)"
  proof
    assume "ext_ok et0 (CpU # cp1) cp2 k"
    then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpU # cp2)) k0" "cp_tr0 et0 cp1 (CpU # cp2) k0"
      "\<forall>y \<in> darts (cpG cp2). k0 y = k y" by (auto simp: ext_ok_def cp_tr0_def)
    define e0 where "e0 = k0 E.X +c a"
    have dU: "darts (cpG (CpU # cp2)) = darts E.GU" using m by simp
    have XU: "E.X \<in> darts (cpG (CpU # cp2))" "E.Xe \<in> darts (cpG (CpU # cp2))"
      "E.n x \<in> darts (cpG (CpU # cp2))" using dU E.x0D by simp_all
    have kXe: "k0 E.Xe = a"
    proof -
      have "fconnect (face (cpG (CpU # cp2))) E.Xe (E.n x)" using m E.cface_GU_Xe by simp
      then have "k0 E.Xe = k0 (E.n x)" using gcol_cface[OF k0(1) XU(2) XU(3)] by simp
      also have "\<dots> = a" using k0(3) c E.nx0D by (simp add: a_def)
      finally show ?thesis .
    qed
    have e0nz: "e0 \<noteq> Color0"
    proof -
      have "adj (cpG (CpU # cp2)) E.X (E.n x)" using m E.adj_GU_X by simp
      then have "k0 E.X \<noteq> k0 (E.n x)" using gcol_adj[OF k0(1) XU(1) XU(3)] by simp
      then show ?thesis using k0(3) c E.nx0D by (simp add: e0_def a_def addc_eq0)
    qed
    have agree: "\<forall>y \<in> darts (cpG (CpU # cp2)). k0 y = k' e0 y"
      using k0(3) c kXe dU by (auto simp: k'_def e0_def)
    have "ext_ok et0 cp1 (CpU # cp2) (k' e0)" using k0(1,2) agree by (auto simp: ext_ok_def)
    then show "ext_ok et0 cp1 (CpU # cp2) (k' Color1) \<or> ext_ok et0 cp1 (CpU # cp2) (k' Color2) \<or>
             ext_ok et0 cp1 (CpU # cp2) (k' Color3)" using e0nz by (cases e0) simp_all
  next
    assume "ext_ok et0 cp1 (CpU # cp2) (k' Color1) \<or> ext_ok et0 cp1 (CpU # cp2) (k' Color2) \<or>
            ext_ok et0 cp1 (CpU # cp2) (k' Color3)"
    then obtain e where "ext_ok et0 cp1 (CpU # cp2) (k' e)" by blast
    then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpU # cp2)) k0" "cp_tr0 et0 cp1 (CpU # cp2) k0"
      "\<forall>y \<in> darts (cpG (CpU # cp2)). k0 y = k' e y" by (auto simp: ext_ok_def)
    have "\<forall>y \<in> darts (cpG cp2). k0 y = k y" using k0(3) m c k'D by auto
    then show "ext_ok et0 (CpU # cp1) cp2 k" using k0(1,2) by (auto simp: ext_ok_def cp_tr0_def)
  qed
  show ?thesis
    unfolding cp_extcol_def et_def[symmetric] cpcolor1.simps h hh_def[symmetric] ext
    using I1 I2 I3 p1 p2 p3 ctree_union_proper ctree_mem_union
    by (simp add: hh_def ctree_mem_union[OF p2 p3] ctree_mem_union[OF p1 ctree_union_proper[OF p2 p3]]
                  ctree_union_proper[OF p1 ctree_union_proper[OF p2 p3]])
qed

lemma (in hypermap) col_node: "coloring G k \<Longrightarrow> y \<in> D \<Longrightarrow> k (n y) \<noteq> k y"
proof -
  assume col: "coloring G k" and y: "y \<in> D"
  have "k (f (e (n y))) = k (e (n y))" using col y by (simp add: coloring_def)
  moreover have "k (e (n y)) \<noteq> k (n y)" using col y by (simp add: coloring_def)
  ultimately show ?thesis by (simp add: nodeK)
qed

lemma (in hypermap) col_face_edge: "coloring G k \<Longrightarrow> y \<in> D \<Longrightarrow> k (f (e y)) = k (e y)"
  by (simp add: coloring_def)

lemma cpcolor1K_correct:
  assumes IH: "\<And>k'. coloring (cpG (CpK # cp2)) k' \<Longrightarrow> cp_extcol et0 cp1 (CpK # cp2) f k'"
    and col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 (CpK # cp1) cp2 (cpcolor1 CpK f) k"
proof -
  obtain G x where c: "cpmap cp2 = (G, x)" by (cases "cpmap cp2")
  interpret E: ecpk G x using hypermap_cpmap[of cp2] cpx_in[of cp2] c by (intro ecpk_intro) simp_all
  have m: "cpmap (CpK # cp2) = (E.GK, E.pK)" using cpmap_Cons_cases(5)[OF c E.ecpk_axioms] .
  have colG: "coloring G k" using col c by simp
  have xD: "x \<in> E.D" by (rule E.x0D)
  define et where "et = trace (map k (cpring_of cp2))"
  define e1 where "e1 = k (E.n x) +c k x"
  define e2 where "e2 = k x +c k (E.f (E.e x))"
  define et2 where "et2 = ptrace (map k (drop 2 (cpring G x) @ [E.n x]))"
  have Det: "et = e1 # e2 # et2"
    using E.trace_cpring_eq[OF colG xD] c by (simp add: et_def e1_def e2_def et2_def cpring_of_def)
  have h: "cprsize (rev (CpK # cp1) @ cp2) = cprsize (rev cp1 @ CpK # cp2)" by simp
  have dK: "darts (cpG (CpK # cp2)) = darts E.GK" using m by simp
  have e12: "e1 = e2 \<longleftrightarrow> k (E.n x) = k (E.f (E.e x))"
    by (simp add: e1_def e2_def addcC[of "k (E.n x)"] addcI)
  show ?thesis
  proof (cases "e1 = e2")
    case True
    have noext: "\<not> ext_ok et0 (CpK # cp1) cp2 k"
    proof
      assume "ext_ok et0 (CpK # cp1) cp2 k"
      then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpK # cp2)) k0"
        "\<forall>y \<in> darts (cpG cp2). k0 y = k y" by (auto simp: ext_ok_def)
      have in1: "E.n x \<in> darts (cpG (CpK # cp2))" "E.f (E.e x) \<in> darts (cpG (CpK # cp2))"
        using dK xD by simp_all
      have "adj E.GK (E.n x) (E.f (E.e x))"
        using E.adj_GK_old[of "E.n x" "E.f (E.e x)"] xD fconnect_step[of "E.f" "E.e x"] by simp
      then have "k0 (E.n x) \<noteq> k0 (E.f (E.e x))" using gcol_adj[OF k0(1) in1] m by simp
      then show False using k0(2) c xD True e12 by simp
    qed
    show ?thesis unfolding cp_extcol_def et_def[symmetric] Det using True noext by simp
  next
    case False
    have ne: "k (E.n x) \<noteq> k (E.e x)" using False e12 E.col_face_edge[OF colG xD] by simp
    define k' where "k' u = (if u = E.X then k (E.n x) else if u = E.K.Xe then k (E.e x) else k u)" for u
    have k'D: "u \<in> E.D \<Longrightarrow> k' u = k u" for u by (simp add: k'_def)
    have lK: "E.K.lng \<longleftrightarrow> E.lng" by (rule E.long_nx0)
    have col': "coloring E.GK k'"
      unfolding coloring_def
    proof (intro conjI ballI)
      fix u assume u: "u \<in> darts E.GK"
      then consider "u \<in> E.D" | "u = E.X" | "u = E.K.Xe" by auto
      then show "k' (edge E.GK u) \<noteq> k' u"
      proof cases
        case 1 then show ?thesis using colG by (simp add: k'_def coloring_def)
      next
        case 2 then show ?thesis using ne by (simp add: k'_def)
      next
        case 3 then show ?thesis using ne by (simp add: k'_def)
      qed
      show "k' (face E.GK u) = k' u"
      proof (cases "u \<in> E.D")
        case True
        show ?thesis
        proof (cases "u = E.e x")
          case True
          then show ?thesis using xD by (simp add: k'_def E.nodeK)
        next
          case nex: False
          show ?thesis
          proof (cases "u = E.e (E.n (E.n x))")
            case True
            have "k (E.e (E.n (E.n x))) = k (E.f (E.e (E.n (E.n x))))"
              using E.col_face_edge[OF colG] xD by simp
            then show ?thesis using True nex xD by (simp add: k'_def E.nodeK)
          next
            case False
            then show ?thesis using True nex colG by (simp add: k'_def E.nodeK coloring_def)
          qed
        qed
      next
        case False
        then consider "u = E.X" | "u = E.K.Xe" using u by auto
        then show ?thesis
        proof cases
          case 1 then show ?thesis using xD by (simp add: k'_def)
        next
          case 2
          show ?thesis
          proof (cases E.lng)
            case True
            then show ?thesis using 2 lK xD E.col_face_edge[OF colG xD] by (simp add: k'_def E.nodeK)
          next
            case False
            have "E.f (E.e x) = E.n x" using False by (simp add: long_cpring_def)
            then show ?thesis using 2 lK False xD E.col_face_edge[OF colG xD] by (simp add: k'_def)
          qed
        qed
      qed
    qed
    have tr: "trace (map k' (cpring_of (CpK # cp2))) = (e1 +c e2) # et2"
    proof -
      have r: "cpring_of (CpK # cp2) = E.X # drop 2 (cpring G x)" using m E.cpring_GK by (simp add: cpring_of_def)
      have dD: "set (drop 2 (cpring G x)) \<subseteq> E.D" using E.ringD by (meson in_set_dropD subsetI subsetD)
      have mp: "map k' (cpring_of (CpK # cp2)) = k (E.n x) # map k (drop 2 (cpring G x))"
        using r dD k'D by (auto simp: k'_def intro!: map_cong)
      have s12: "e1 +c e2 = k (E.n x) +c k (E.f (E.e x))"
        by (simp add: e1_def e2_def addcA)
      show ?thesis
      proof (cases "drop 2 (cpring G x)")
        case Nil
        then have "\<not> E.lng" using E.size_long_cpring by simp
        then have "E.f (E.e x) = E.n x" by (simp add: long_cpring_def)
        then show ?thesis using mp Nil s12 by (simp add: et2_def trace_def ptrace_def ctrace_def)
      next
        case (Cons z p)
        have "\<not> length (cpring G x) \<le> 2" using Cons drop_eq_Nil[of 2 "cpring G x"] by force
        then have lg: E.lng using E.size_long_cpring by simp
        have hl: "cpring G x = E.n x # x # E.f (E.e x) # drop 3 (cpring G x)" by (rule E.head_long_cpring[OF lg])
        have "drop 2 (cpring G x) = E.f (E.e x) # drop 3 (cpring G x)"
          using arg_cong[OF hl, of "drop 2"] by (simp add: numeral_2_eq_2)
        then have z: "z = E.f (E.e x)" using Cons by simp
        show ?thesis using mp Cons z s12 by (simp add: et2_def trace_Cons ptrace_def)
      qed
    qed
    have I: "cp_extcol et0 cp1 (CpK # cp2) f k'" using IH[of k'] col' m by simp
    have ext: "ext_ok et0 (CpK # cp1) cp2 k \<longleftrightarrow> ext_ok et0 cp1 (CpK # cp2) k'"
    proof
      assume "ext_ok et0 (CpK # cp1) cp2 k"
      then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpK # cp2)) k0" "cp_tr0 et0 cp1 (CpK # cp2) k0"
        "\<forall>y \<in> darts (cpG cp2). k0 y = k y" by (auto simp: ext_ok_def cp_tr0_def)
      have in1: "E.X \<in> darts (cpG (CpK # cp2))" "E.K.Xe \<in> darts (cpG (CpK # cp2))"
        "E.n x \<in> darts (cpG (CpK # cp2))" "E.e x \<in> darts (cpG (CpK # cp2))" using dK xD by simp_all
      have "fconnect (face (cpG (CpK # cp2))) E.X (E.n x)" using m E.K.cface_GN_X by simp
      then have kX: "k0 E.X = k (E.n x)" using gcol_cface[OF k0(1) in1(1) in1(3)] k0(3) c xD by simp
      have "fconnect (face (cpG (CpK # cp2))) E.K.Xe (E.e x)" using m E.K.cface_GN_Xe by (simp add: E.nodeK)
      then have kXe: "k0 E.K.Xe = k (E.e x)" using gcol_cface[OF k0(1) in1(2) in1(4)] k0(3) c xD by simp
      have "\<forall>y \<in> darts (cpG (CpK # cp2)). k0 y = k' y" using k0(3) c kX kXe dK by (auto simp: k'_def)
      then show "ext_ok et0 cp1 (CpK # cp2) k'" using k0(1,2) by (auto simp: ext_ok_def)
    next
      assume "ext_ok et0 cp1 (CpK # cp2) k'"
      then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpK # cp2)) k0" "cp_tr0 et0 cp1 (CpK # cp2) k0"
        "\<forall>y \<in> darts (cpG (CpK # cp2)). k0 y = k' y" by (auto simp: ext_ok_def)
      have "\<forall>y \<in> darts (cpG cp2). k0 y = k y" using k0(3) dK c k'D by auto
      then show "ext_ok et0 (CpK # cp1) cp2 k" using k0(1,2) by (auto simp: ext_ok_def cp_tr0_def)
    qed
    show ?thesis using I False unfolding cp_extcol_def et_def[symmetric] Det h ext tr by simp
  qed
qed

lemma cpcolor1A_correct:
  assumes IH: "\<And>k'. coloring (cpG (CpA # cp2)) k' \<Longrightarrow> cp_extcol et0 cp1 (CpA # cp2) f k'"
    and col: "coloring (cpG cp2) k"
  shows "cp_extcol et0 (CpA # cp1) cp2 (cpcolor1 CpA f) k"
proof -
  obtain G x where c: "cpmap cp2 = (G, x)" by (cases "cpmap cp2")
  interpret E: ecpa G x using hypermap_cpmap[of cp2] cpx_in[of cp2] c by (intro ecpa_intro) simp_all
  have m: "cpmap (CpA # cp2) = (E.GA, E.pA)" using cpmap_Cons_cases(6)[OF c E.ecpa_axioms] .
  have colG: "coloring G k" using col c by simp
  have xD: "x \<in> E.D" by (rule E.x0D)
  define et where "et = trace (map k (cpring_of cp2))"
  define e1 where "e1 = k (E.n x) +c k x"
  define e2 where "e2 = k x +c k (E.f (E.e x))"
  define et2 where "et2 = ptrace (map k (drop 2 (cpring G x) @ [E.n x]))"
  have Det: "et = e1 # e2 # et2"
    using E.trace_cpring_eq[OF colG xD] c by (simp add: et_def e1_def e2_def et2_def cpring_of_def)
  have h: "cprsize (rev (CpA # cp1) @ cp2) = cprsize (rev cp1 @ CpA # cp2)" by simp
  have dA: "darts (cpG (CpA # cp2)) = darts (cpG cp2)" using m c by simp
  have e12: "e1 = e2 \<longleftrightarrow> k (E.n x) = k (E.f (E.e x))"
    by (simp add: e1_def e2_def addcC[of "k (E.n x)"] addcI)
  show ?thesis
  proof (cases "e1 = e2")
    case False
    have noext: "\<not> ext_ok et0 (CpA # cp1) cp2 k"
    proof
      assume "ext_ok et0 (CpA # cp1) cp2 k"
      then obtain k0 where k0: "coloring (cpG (rev cp1 @ CpA # cp2)) k0"
        "\<forall>y \<in> darts (cpG cp2). k0 y = k y" by (auto simp: ext_ok_def)
      have in1: "E.f (E.e x) \<in> darts (cpG (CpA # cp2))" "E.n x \<in> darts (cpG (CpA # cp2))"
        using dA c xD by simp_all
      have "fconnect (face (cpG (CpA # cp2))) (E.f (E.e x)) (E.n x)" using m E.ecpA_merge by simp
      then have "k0 (E.f (E.e x)) = k0 (E.n x)" using gcol_cface[OF k0(1) in1] by simp
      then show False using k0(2) c xD False e12 by simp
    qed
    show ?thesis unfolding cp_extcol_def et_def[symmetric] Det using False noext by simp
  next
    case True
    have eq: "k (E.n x) = k (E.f (E.e x))" using True e12 by simp
    have col': "coloring E.GA k"
      unfolding coloring_def
    proof (intro conjI ballI)
      fix u assume u: "u \<in> darts E.GA"
      then have uD: "u \<in> E.D" by simp
      show "k (edge E.GA u) \<noteq> k u"
      proof (cases E.cc)
        case False then show ?thesis using colG uD by (simp add: coloring_def)
      next
        case cc: True
        show ?thesis
        proof (cases "u = x")
          case True
          have "k (E.e (E.n (E.n x))) = k (E.n x)"
            using E.col_face_edge[OF colG, of "E.n (E.n x)"] xD by (simp add: E.nodeK)
          then show ?thesis using True cc E.col_node[OF colG xD] by simp
        next
          case nx: False
          show ?thesis
          proof (cases "u = E.n (E.n x)")
            case True
            have "k (E.e x) = k (E.n x)" using E.col_face_edge[OF colG xD] eq by simp
            then show ?thesis using True nx cc E.col_node[OF colG, of "E.n x"] xD by simp
          next
            case False then show ?thesis using nx cc colG uD by (simp add: coloring_def)
          qed
        qed
      qed
      show "k (face E.GA u) = k u"
      proof (cases E.cc)
        case True then show ?thesis using colG uD by (simp add: coloring_def)
      next
        case False
        have kex: "k (E.e x) = k (E.n x)" using E.col_face_edge[OF colG xD] eq by simp
        show ?thesis
        proof (cases "u = E.e x")
          case True then show ?thesis using False kex by simp
        next
          case ne: False
          have "k (E.f u) = k u" using colG uD by (simp add: coloring_def)
          then show ?thesis using False ne eq by (cases "E.f u = E.n x") simp_all
        qed
      qed
    qed
    have tr: "trace (map k (cpring_of (CpA # cp2))) = (if et2 = [] then et else et2)"
    proof (cases "long_cpring G x")
      case True
      have hl: "cpring G x = E.n x # x # E.f (E.e x) # drop 3 (cpring G x)" by (rule E.head_long_cpring[OF True])
      have "drop 2 (cpring G x) = E.f (E.e x) # drop 3 (cpring G x)"
        using arg_cong[OF hl, of "drop 2"] by (simp add: numeral_2_eq_2)
      then obtain rest where rr: "drop 2 (cpring G x) = E.f (E.e x) # rest" by blast
      have r: "cpring_of (CpA # cp2) = drop 2 (cpring G x)" using m True E.cpring_GA by (simp add: cpring_of_def)
      have e2eq: "et2 = pairmap addc (k (E.f (E.e x))) (map k rest @ [k (E.n x)])"
        using rr by (simp add: et2_def ptrace_def)
      have "length et2 = Suc (length rest)" using rr by (simp add: et2_def ptrace_def)
      then have ne: "et2 \<noteq> []" by auto
      have "trace (map k (cpring_of (CpA # cp2))) = et2" using r rr e2eq eq by (simp add: trace_Cons)
      then show ?thesis using ne by simp
    next
      case False
      have r: "cpring_of (CpA # cp2) = cpring G x" using m False E.cpring_GA by (simp add: cpring_of_def)
      have "drop 2 (cpring G x) = []" using False E.size_long_cpring by simp
      then have "et2 = []" by (simp add: et2_def ptrace_def)
      then show ?thesis using r c by (simp add: et_def cpring_of_def)
    qed
    have I: "cp_extcol et0 cp1 (CpA # cp2) f k" using IH[of k] col' m by simp
    have ext: "ext_ok et0 (CpA # cp1) cp2 k \<longleftrightarrow> ext_ok et0 cp1 (CpA # cp2) k"
      using dA by (simp add: ext_ok_def cp_tr0_def)
    have T: "trace (map k (cpring_of (CpA # cp2))) = (if et2 = [] then e1 # e2 # et2 else et2)"
      using tr Det by simp
    have gf: "cpcolor1 CpA f (trace (map k (cpring_of cp2))) = f (trace (map k (cpring_of (CpA # cp2))))"
      using T True Det unfolding et_def by simp
    show ?thesis using I unfolding cp_extcol_def gf h ext .
  qed
qed

section \<open>Expanding Y and H steps\<close>

lemma cpmap_append_cong: "cpmap cp = cpmap cp' \<Longrightarrow> cpmap (l @ cp) = cpmap (l @ cp')"
proof (induction l)
  case (Cons s l)
  then show ?case by (cases s) simp_all
qed simp

lemma cpmap_expY: "cpmap (CpR' # CpK # CpR 1 # CpU # cp) = cpmap (CpY # cp)"
proof -
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp2 G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp2_intro) simp_all
  have hU: "hypermap (ecpU G x)" using E.hypermap_GU by (simp add: E.GU_def)
  have hY: "hypermap (ecpN (ecpU G x) (ecpX G))" using E.T.hypermap_GN by (simp add: E.GY_eq)
  have r1: "(node (ecpU G x) ^^ (order (node (ecpU G x)) (ecpX G) - 1)) (ecpX G) =
            face (ecpU G x) (edge (ecpU G x) (ecpX G))"
    using hypermap.ecpR1_eq[OF hU] hypermap.ecpR_ptr_def[OF hU] by simp
  have k1: "node (ecpU G x) (face (ecpU G x) (edge (ecpU G x) (ecpX G))) = ecpX G"
    by (rule hypermap.edgeK[OF hU])
  have k2: "node (ecpN (ecpU G x) (ecpX G)) (face (ecpN (ecpU G x) (ecpX G))
              (edge (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))) = ecpX (ecpU G x)"
    by (rule hypermap.edgeK[OF hY])
  show ?thesis using c r1 k1 k2 by simp
qed

lemma cpmap_expH: "cpmap (CpR' # CpK # CpK # CpR 1 # CpU # cp) = cpmap (CpH # cp)"
proof -
  obtain G x where c: "cpmap cp = (G, x)" by (cases "cpmap cp")
  interpret E: ecp2h G x using hypermap_cpmap[of cp] cpx_in[of cp] c by (intro ecp2h_intro) simp_all
  have hU: "hypermap (ecpU G x)" using E.hypermap_GU by (simp add: E.GU_def)
  have hY: "hypermap (ecpN (ecpU G x) (ecpX G))" using E.T.hypermap_GN by (simp add: E.GY_eq)
  interpret H: ecp "ecpN (ecpU G x) (ecpX G)" "ecpX (ecpU G x)"
    using hY E.XY_in by (intro ecp_intro) (simp_all add: E.GY_eq E.XY_eq)
  have hH: "hypermap (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))"
    using H.hypermap_GN by (simp add: H.GN_def)
  have r1: "(node (ecpU G x) ^^ (order (node (ecpU G x)) (ecpX G) - 1)) (ecpX G) =
            face (ecpU G x) (edge (ecpU G x) (ecpX G))"
    using hypermap.ecpR1_eq[OF hU] hypermap.ecpR_ptr_def[OF hU] by simp
  have k1: "node (ecpU G x) (face (ecpU G x) (edge (ecpU G x) (ecpX G))) = ecpX G"
    by (rule hypermap.edgeK[OF hU])
  have k2: "node (ecpN (ecpU G x) (ecpX G)) (face (ecpN (ecpU G x) (ecpX G))
              (edge (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))) = ecpX (ecpU G x)"
    by (rule hypermap.edgeK[OF hY])
  have k3: "node (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))
              (face (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))
                (edge (ecpN (ecpN (ecpU G x) (ecpX G)) (ecpX (ecpU G x)))
                   (ecpX (ecpN (ecpU G x) (ecpX G))))) = ecpX (ecpN (ecpU G x) (ecpX G))"
    by (rule hypermap.edgeK[OF hH])
  show ?thesis using c r1 k1 k2 k3 by simp
qed

lemma rotr1_snoc: "rotr1 (l @ [c]) = c # l"
  by (simp add: rotr1_def rot_def)

lemma cpcolor1_expY:
  assumes "e1 \<noteq> Color0"
  shows "cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpR' F))) (e1 # et) =
         cpcolor1 CpY F (e1 # et)"
proof -
  have g: "cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpR' F)) (c # c # e1 # et) =
           (if c = e1 then CtreeEmpty else F (c # (c +c e1) # et))" for c
    by (simp add: rot_Suc0_Cons rotr1_snoc[of "(c +c e1) # et" c, simplified])
  show ?thesis unfolding cpcolor1.simps(3) g using assms by (cases e1) (simp_all add: ctree_union_sym)
qed

lemma cpcolor1_expH:
  assumes "e1 \<noteq> Color0" "e2 \<noteq> Color0"
  shows "cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F)))) (e1 # e2 # et) =
         cpcolor1 CpH F (e1 # e2 # et)"
proof -
  have g: "cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F))) (c # c # e1 # e2 # et) =
           (if c = e1 then CtreeEmpty else if c +c e1 = e2 then CtreeEmpty
            else F (c # (c +c e1 +c e2) # et))" for c
    by (simp add: rot_Suc0_Cons rotr1_snoc[of "(c +c e1 +c e2) # et" c, simplified])
  show ?thesis unfolding cpcolor1.simps(3) g using assms by (cases e1; cases e2) (simp_all add: ctree_union_sym)
qed

lemma ext_cong:
  assumes "cpmap (rev A @ cp2) = cpmap (rev B @ cp2)"
  shows "cp_extcol et0 A cp2 f k \<longleftrightarrow> cp_extcol et0 B cp2 f k"
proof -
  have "cprsize (rev A @ cp2) = cprsize (rev B @ cp2)"
    using size_ring_cpmap[of "rev A @ cp2"] size_ring_cpmap[of "rev B @ cp2"] assms
    by (simp add: cpring_of_def)
  then show ?thesis using assms by (simp add: cp_extcol_def ext_ok_def cp_tr0_def cpring_of_def)
qed

lemma trace_cpmap_no0:
  "coloring (cpG cp2) k \<Longrightarrow> Color0 \<notin> set (trace (map k (cpring_of cp2)))"
  using hypermap.memc0_trace_cpring[OF hypermap_cpmap _ cpx_in] by (simp add: cpring_of_def)

lemma trace_cpmap_shape:
  assumes "coloring (cpG cp2) k"
  obtains e1 e2 et where "trace (map k (cpring_of cp2)) = e1 # e2 # et" "e1 \<noteq> Color0" "e2 \<noteq> Color0"
proof -
  interpret H: hypermap "cpG cp2" by (rule hypermap_cpmap)
  have t: "trace (map k (cpring_of cp2)) = (k (H.n (cpx cp2)) +c k (cpx cp2)) #
        (k (cpx cp2) +c k (H.f (H.e (cpx cp2)))) # ptrace (map k (drop 2 (cpring_of cp2) @ [H.n (cpx cp2)]))"
    using H.trace_cpring_eq[OF assms cpx_in] by (simp add: cpring_of_def)
  show ?thesis using that[OF t] trace_cpmap_no0[OF assms] unfolding t by (simp add: eq_commute[of Color0])
qed

theorem cpcolor1_correct:
  "coloring (cpG cp2) k \<Longrightarrow> cp_extcol et0 cp1 cp2 (foldr cpcolor1 cp1 cpbranch) k"
proof (induction cp1 arbitrary: cp2 k)
  case Nil
  then show ?case using cpbranch_correct by simp
next
  case (Cons s cp1)
  define F where "F = foldr cpcolor1 cp1 cpbranch"
  have IH: "\<And>cp2' k'. coloring (cpG cp2') k' \<Longrightarrow> cp_extcol et0 cp1 cp2' F k'"
    using Cons.IH unfolding F_def .
  have fs: "foldr cpcolor1 (s # cp1) cpbranch = cpcolor1 s F" by (simp add: F_def)
  have "cp_extcol et0 (s # cp1) cp2 (cpcolor1 s F) k"
  proof (cases s)
    case (CpR m) show ?thesis unfolding CpR by (rule cpcolor1R_correct[OF IH Cons.prems])
  next
    case CpR' show ?thesis unfolding CpR' by (rule cpcolor1R'_correct[OF IH Cons.prems])
  next
    case CpU show ?thesis unfolding CpU by (rule cpcolor1U_correct[OF IH Cons.prems])
  next
    case CpK show ?thesis unfolding CpK by (rule cpcolor1K_correct[OF IH Cons.prems])
  next
    case CpA show ?thesis unfolding CpA by (rule cpcolor1A_correct[OF IH Cons.prems])
  next
    case CpY
    have c4: "\<And>k4. coloring (cpG (CpK # CpR 1 # CpU # cp2)) k4 \<Longrightarrow>
        cp_extcol et0 (CpR' # cp1) (CpK # CpR 1 # CpU # cp2) (cpcolor1 CpR' F) k4"
      by (rule cpcolor1R'_correct[OF IH])
    have c3: "\<And>k3. coloring (cpG (CpR 1 # CpU # cp2)) k3 \<Longrightarrow>
        cp_extcol et0 (CpK # CpR' # cp1) (CpR 1 # CpU # cp2) (cpcolor1 CpK (cpcolor1 CpR' F)) k3"
      by (rule cpcolor1K_correct[OF c4])
    have c2: "\<And>k2. coloring (cpG (CpU # cp2)) k2 \<Longrightarrow>
        cp_extcol et0 (CpR 1 # CpK # CpR' # cp1) (CpU # cp2) (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpR' F))) k2"
      by (rule cpcolor1R_correct[OF c3])
    have chain: "cp_extcol et0 (CpU # CpR 1 # CpK # CpR' # cp1) cp2
        (cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpR' F)))) k"
      by (rule cpcolor1U_correct[OF c2 Cons.prems])
    have mm: "cpmap (rev (CpU # CpR 1 # CpK # CpR' # cp1) @ cp2) = cpmap (rev (CpY # cp1) @ cp2)"
      using cpmap_append_cong[OF cpmap_expY, of "rev cp1" cp2] by simp
    obtain e1 e2 et where t: "trace (map k (cpring_of cp2)) = e1 # e2 # et" "e1 \<noteq> Color0"
      using trace_cpmap_shape[OF Cons.prems] by blast
    have fe: "cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpR' F))) (trace (map k (cpring_of cp2)))
              = cpcolor1 CpY F (trace (map k (cpring_of cp2)))"
      unfolding t(1) by (rule cpcolor1_expY[OF t(2)])
    show ?thesis using chain unfolding ext_cong[OF mm] unfolding CpY cp_extcol_def fe .
  next
    case CpH
    have c5: "\<And>k5. coloring (cpG (CpK # CpK # CpR 1 # CpU # cp2)) k5 \<Longrightarrow>
        cp_extcol et0 (CpR' # cp1) (CpK # CpK # CpR 1 # CpU # cp2) (cpcolor1 CpR' F) k5"
      by (rule cpcolor1R'_correct[OF IH])
    have c4: "\<And>k4. coloring (cpG (CpK # CpR 1 # CpU # cp2)) k4 \<Longrightarrow>
        cp_extcol et0 (CpK # CpR' # cp1) (CpK # CpR 1 # CpU # cp2) (cpcolor1 CpK (cpcolor1 CpR' F)) k4"
      by (rule cpcolor1K_correct[OF c5])
    have c3: "\<And>k3. coloring (cpG (CpR 1 # CpU # cp2)) k3 \<Longrightarrow>
        cp_extcol et0 (CpK # CpK # CpR' # cp1) (CpR 1 # CpU # cp2)
          (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F))) k3"
      by (rule cpcolor1K_correct[OF c4])
    have c2: "\<And>k2. coloring (cpG (CpU # cp2)) k2 \<Longrightarrow>
        cp_extcol et0 (CpR 1 # CpK # CpK # CpR' # cp1) (CpU # cp2)
          (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F)))) k2"
      by (rule cpcolor1R_correct[OF c3])
    have chain: "cp_extcol et0 (CpU # CpR 1 # CpK # CpK # CpR' # cp1) cp2
        (cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F))))) k"
      by (rule cpcolor1U_correct[OF c2 Cons.prems])
    have mm: "cpmap (rev (CpU # CpR 1 # CpK # CpK # CpR' # cp1) @ cp2) = cpmap (rev (CpH # cp1) @ cp2)"
      using cpmap_append_cong[OF cpmap_expH, of "rev cp1" cp2] by simp
    obtain e1 e2 et where t: "trace (map k (cpring_of cp2)) = e1 # e2 # et" "e1 \<noteq> Color0" "e2 \<noteq> Color0"
      using trace_cpmap_shape[OF Cons.prems] by blast
    have fe: "cpcolor1 CpU (cpcolor1 (CpR 1) (cpcolor1 CpK (cpcolor1 CpK (cpcolor1 CpR' F))))
                (trace (map k (cpring_of cp2))) = cpcolor1 CpH F (trace (map k (cpring_of cp2)))"
      unfolding t(1) by (rule cpcolor1_expH[OF t(2,3)])
    show ?thesis using chain unfolding ext_cong[OF mm] unfolding CpH cp_extcol_def fe .
  qed
  then show ?case unfolding fs .
qed

section \<open>Main theorems\<close>

definition kbase :: "nat \<Rightarrow> color" where
  "kbase x = (if x = 0 then Color2 else Color3)"

lemma coloring_kbase: "coloring cpmap0 kbase"
  by (auto simp: coloring_def kbase_def sw01_def)

lemma trace_kbase: "trace (map kbase (cpring_of [])) = [Color1, Color1]"
  using cpring0 by (simp add: cpring_of_def kbase_def trace_def ptrace_def ctrace_def)

lemma cpcolor0_extcol:
  "ctree_proper (cprsize cp - 2) (cpcolor0 (rev cp)) \<and>
   (ctree_mem (cpcolor0 (rev cp)) (ttail et0) \<longleftrightarrow> ext_ok et0 (rev cp) [] kbase)"
  using cpcolor1_correct[of "[]" kbase et0 "rev cp"] coloring_kbase trace_kbase
  by (simp add: cp_extcol_def cpcolor0_def cpcol_def)

lemma trace_head_sum: "lc \<noteq> [] \<Longrightarrow> trace lc = sumt (tl (trace lc)) # tl (trace lc)"
proof -
  assume "lc \<noteq> []"
  then have "trace lc \<noteq> []" by (metis length_0_conv length_trace)
  then obtain a t where t: "trace lc = a # t" by (cases "trace lc") auto
  have "a +c sumt t = Color0" using sumt_trace[of lc] t by simp
  then have "a = sumt t" by (simp add: addc_eq0)
  then show ?thesis using t by simp
qed

lemma ext_ok_base:
  "ext_ok et0 (rev cp) [] kbase \<longleftrightarrow>
   (\<exists>k0. coloring (cpG cp) k0 \<and> ttail et0 = eptrace (rot 1 (map k0 (cpring_of cp))))"
proof
  assume "ext_ok et0 (rev cp) [] kbase"
  then show "\<exists>k0. coloring (cpG cp) k0 \<and> ttail et0 = eptrace (rot 1 (map k0 (cpring_of cp)))"
    by (auto simp: ext_ok_def cp_tr0_def)
next
  assume "\<exists>k0. coloring (cpG cp) k0 \<and> ttail et0 = eptrace (rot 1 (map k0 (cpring_of cp)))"
  then obtain k0 where k0: "coloring (cpG cp) k0" "ttail et0 = eptrace (rot 1 (map k0 (cpring_of cp)))"
    by blast
  have col: "coloring (cpG (rev (rev cp) @ [])) k0" using k0(1) by simp
  have d01: "0 \<in> darts (cpG [])" "1 \<in> darts (cpG [])" by simp_all
  have a01: "adj (cpG []) 0 1"
  proof -
    interpret M: hypermap cpmap0 by (rule hypermap_cpmap0)
    have "edge cpmap0 0 = 1" by (simp add: sw01_def)
    then show ?thesis using M.adjE[of 0] by simp
  qed
  have ne: "k0 0 \<noteq> k0 1" using gcol_adj[OF col d01 a01] .
  define d where "d = k0 0 +c k0 1"
  have dnz: "d \<noteq> Color0" using ne by (simp add: d_def addc_eq0)
  define h where "h = edge_rot d"
  have hd: "permc h d = Color1" by (simp add: h_def edge_rot_self[OF dnz])
  define c where "c = Color2 +c permc h (k0 0)"
  define k1 where "k1 x = c +c permc h (k0 x)" for x
  have g: "coloring (cpG cp) k1 \<and> ttail et0 = eptrace (rot 1 (map k1 (cpring_of cp)))"
    unfolding k1_def by (rule gcol_perm[OF k0])
  have k10: "k1 0 = Color2" by (simp add: k1_def c_def addcA)
  have k11: "k1 1 = Color3"
  proof -
    have "k1 1 = Color2 +c (permc h (k0 0) +c permc h (k0 1))" by (simp add: k1_def c_def addcA)
    also have "\<dots> = Color2 +c permc h d" by (simp add: d_def permc_addc)
    finally show ?thesis using hd by simp
  qed
  have "\<forall>x \<in> darts (cpG []). k1 x = kbase x" using k10 k11 by (auto simp: kbase_def)
  then show "ext_ok et0 (rev cp) [] kbase" using g by (auto simp: ext_ok_def cp_tr0_def)
qed

lemma eptrace_trace_iff:
  assumes h: "hypermap G" and x: "x \<in> darts G"
  shows "(\<exists>k0. coloring G k0 \<and> ttail et = eptrace (rot 1 (map k0 (cpring G x)))) \<longleftrightarrow>
         even_trace et \<and> ring_trace G (cpring G x) (sumt et # et)"
proof
  interpret H: hypermap G by (rule h)
  assume "\<exists>k0. coloring G k0 \<and> ttail et = eptrace (rot 1 (map k0 (cpring G x)))"
  then obtain k0 where col: "coloring G k0" and tr: "ttail et = eptrace (rot 1 (map k0 (cpring G x)))"
    by blast
  define t where "t = tl (trace (map k0 (cpring G x)))"
  have te: "ttail et = etail t" using tr by (simp add: t_def eptrace_def tl_trace_ptrace)
  have tp: "proper_trace t" unfolding t_def by (rule H.proper_trace_cpring[OF col x])
  have t0: "Color0 \<notin> set t" using H.memc0_trace_cpring[OF col x] unfolding t_def
    by (cases "trace (map k0 (cpring G x))") auto
  have et0: "Color0 \<notin> set (etail t)" using tp t0 memc0_ttail[of t] by (simp add: etail_def)
  have pe: "proper_trace et"
  proof (rule ccontr)
    assume "\<not> proper_trace et"
    then have "ttail et = [Color0]" by (simp add: ttail_def)
    then show False using te et0 by simp
  qed
  have ev: "even_trace et" using te even_etail[of t] by (simp add: even_trace_def)
  have ee: "etail et = ttail et" using ev by (simp add: etail_def etrace_perm_def)
  obtain g1 where g1: "permt g1 et = Color1 # ttail et" using etail_perm[OF pe] ee by auto
  obtain g2 where g2: "permt g2 t = Color1 # ttail et" using etail_perm[OF tp] te by auto
  obtain hh where hh: "permt hh t = permt (inv_eperm g1) (permt g2 t)" using compose_permt by blast
  have inv1: "permt (inv_eperm g1) (permt g1 et) = et" by (induction et) simp_all
  have hte: "permt hh t = et" using hh g1 g2 inv1 by simp
  define k where "k y = permc hh (k0 y)" for y
  have colk: "coloring G k" using col by (simp add: coloring_def k_def permc_inj)
  have ne: "map k0 (cpring G x) \<noteq> []" using H.cpring_ne by simp
  have mk: "map k (cpring G x) = permt hh (map k0 (cpring G x))" by (simp add: k_def permt_def)
  have "trace (map k (cpring G x)) = permt hh (trace (map k0 (cpring G x)))"
    unfolding mk by (rule trace_permt)
  also have "trace (map k0 (cpring G x)) = sumt t # t" unfolding t_def by (rule trace_head_sum[OF ne])
  also have "permt hh (sumt t # t) = sumt et # et" using hte by (simp add: sumt_permt[symmetric])
  finally show "even_trace et \<and> ring_trace G (cpring G x) (sumt et # et)"
    using ev colk by (auto simp: ring_trace_def)
next
  assume a: "even_trace et \<and> ring_trace G (cpring G x) (sumt et # et)"
  then obtain k where col: "coloring G k" and tr: "sumt et # et = trace (map k (cpring G x))"
    by (auto simp: ring_trace_def)
  have tle: "tl (trace (map k (cpring G x))) = et" using tr by (metis list.sel(3))
  have "eptrace (rot 1 (map k (cpring G x))) = etail et"
    using tle tl_trace_ptrace[of "map k (cpring G x)"] by (simp add: eptrace_def)
  also have "\<dots> = ttail et" using a by (simp add: etail_def etrace_perm_def)
  finally show "\<exists>k0. coloring G k0 \<and> ttail et = eptrace (rot 1 (map k0 (cpring G x)))"
    using col by metis
qed

theorem ctree_mem_cpcolor:
  "ctree_mem (cpcolor cp) et \<longleftrightarrow> even_trace et \<and> ring_trace (cpG cp) (cpring_of cp) (sumt et # et)"
proof -
  have "ctree_mem (cpcolor cp) et \<longleftrightarrow> ctree_mem (cpcolor0 (rev cp)) (ttail et)"
    by (simp add: cpcolor_def ctree_mem_cons_rot)
  also have "\<dots> \<longleftrightarrow> ext_ok et (rev cp) [] kbase" using cpcolor0_extcol by blast
  also have "\<dots> \<longleftrightarrow> even_trace et \<and> ring_trace (cpG cp) (cpring_of cp) (sumt et # et)"
    unfolding ext_ok_base cpring_of_def by (rule eptrace_trace_iff[OF hypermap_cpmap cpx_in])
  finally show ?thesis .
qed

theorem cpcolor_proper: "ctree_proper (cprsize cp - 1) (cpcolor cp)"
proof (cases "2 \<le> cprsize cp")
  case True
  have "ctree_proper (cprsize cp - 2) (cpcolor0 (rev cp))" using cpcolor0_extcol by blast
  then have "ctree_proper (Suc (cprsize cp - 2)) (cpcolor cp)"
    unfolding cpcolor_def by (rule ctree_cons_rot_proper)
  moreover have "Suc (cprsize cp - 2) = cprsize cp - 1" using True by simp
  ultimately show ?thesis by simp
next
  case False
  define t where "t = cpcolor0 (rev cp)"
  have p0: "ctree_proper 0 t" using cpcolor0_extcol[of cp] False by (simp add: t_def)
  have "t = CtreeEmpty"
  proof (cases t)
    case (CtreeLeaf lf)
    have tt: "ttail [Color1] = []" by (simp add: ttail_def proper_trace_def head_color_def)
    have "ctree_mem t []" using CtreeLeaf by (simp add: ctree_mem_leaf)
    then have "ext_ok [Color1] (rev cp) [] kbase" using cpcolor0_extcol[of cp "[Color1]"] tt
      by (simp add: t_def)
    then obtain k0 where "coloring (cpG cp) k0" by (auto simp: ext_ok_def)
    then have "proper_cpring (cpG cp) (cpx cp)"
      using hypermap.coloring_proper_cpring[OF hypermap_cpmap _ cpx_in] by blast
    then have "2 \<le> cprsize cp"
      using hypermap.size_proper_cpring[OF hypermap_cpmap] size_ring_cpmap[of cp]
      by (simp add: cpring_of_def)
    then show ?thesis using False by simp
  next
    case (CtreeNode a b c)
    then show ?thesis using p0 by simp
  qed simp
  then show ?thesis by (simp add: cpcolor_def t_def ctree_cons_rot_def ctree_cons_def)
qed

end
