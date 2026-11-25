(* Upstream attribution for adapted material:
   (c) Copyright 2006-2018 Microsoft Corporation and Inria.
   Distributed under the terms of CeCILL-B.
   Isabelle/HOL development: see AUTHORS and NOTICE; licensing: see LICENSE. *)
(*  Title:      Initgtree.thy
    The initial tree of balanced (partial) chromograms.
    Ported from G. Gonthier's Coq development (initgtree.v).
*)
theory Initgtree
  imports Four_Colour_Maps.Gtree Four_Colour_Maps.Initctree
begin

type_synonym gtree_table = "gtree_pair list"

definition init_gtree_h1 :: gtree_table where
  "init_gtree_h1 = [GtreePair GtreeLeaf01 GtreeLeaf0, GtreePair GtreeLeaf13 GtreeLeaf12,
                    GtreePair GtreeLeaf23 GtreeLeaf23]"

fun gtree_merge_pairs :: "gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair" where
  "gtree_merge_pairs (GtreePair t0 t0') (GtreePair t1 t1') (GtreePair t2 t3) =
     GtreePair (GtreeNode t0 t1' t2 t3) (GtreeNode t0' t1 t3 t2)"

fun gtree_merge_line :: "gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_pair \<Rightarrow> gtree_table \<Rightarrow> nat \<Rightarrow> gtree_table" where
  "gtree_merge_line pt0 pt1 pt2 lpt 0 = [gtree_merge_pairs pt0 pt1 pt2]"
| "gtree_merge_line pt0 pt1 pt2 [] (Suc d) =
     [gtree_merge_pairs pt0 pt1 pt2, gtree_merge_pairs empty_gtree_pair pt0 pt1,
      gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0]"
| "gtree_merge_line pt0 pt1 pt2 (pt # lpt) (Suc d) =
     gtree_merge_pairs pt0 pt1 pt2 # gtree_merge_line pt pt0 pt1 lpt d"

fun gtree_init_table :: "nat \<Rightarrow> nat \<Rightarrow> gtree_table" where
  "gtree_init_table d 0 = init_gtree_h1"
| "gtree_init_table d (Suc h) = (case gtree_init_table (Suc d) h of
      pt1 # pt0 # lpt \<Rightarrow> gtree_merge_line pt0 pt1 empty_gtree_pair lpt d
    | tab \<Rightarrow> tab)"

definition gtree_init_tree :: "nat \<Rightarrow> gtree" where
  "gtree_init_tree h = (case h of 0 \<Rightarrow> GtreeEmpty
     | Suc h' \<Rightarrow> (case gtree_init_table 0 h' of GtreePair t _ # _ \<Rightarrow> t | _ \<Rightarrow> GtreeEmpty))"

definition init_gtree_spec :: "nat \<Rightarrow> chromogram \<Rightarrow> bool" where
  "init_gtree_spec h w \<longleftrightarrow> length w = h \<and> gram_balanced 0 False (cgram 0 False w)"

definition gtsub :: "gtree_table \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gtree" where
  "gtsub tab n b = (if n < length tab then gtree_pair_sub (tab ! n) b else GtreeEmpty)"

section \<open>Counting balanced chromograms\<close>

definition spec' :: "nat \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> chromogram \<Rightarrow> bool" where
  "spec' h lb b0 w \<longleftrightarrow> length w = h \<and> gram_balanced (length lb) b0 (cgram (length lb) b0 w)"

lemma gram_balanced_cgram_Nil:
  "gram_balanced d b (cgram d b []) \<longleftrightarrow> (d = 0 \<and> b) \<or> d = 1"
  by (cases d; cases "d - 1"; cases b) simp_all

lemma gen_dyck_ge3_0: "3 \<le> m \<Longrightarrow> gen_dyck m 0 = 0" by simp
lemma gen_dyck_ge3_1: "3 \<le> m \<Longrightarrow> gen_dyck m 1 = 0"
  by (cases m) (simp_all add: gen_dyck_max)

lemma match_count_len0:
  "(\<And>w. st w \<Longrightarrow> length w \<noteq> length et) \<Longrightarrow> match_count st lb et = 0"
  using match_countP matchpg_size by metis

lemma match_count_cong: "(\<And>w. st w = st' w) \<Longrightarrow> match_count st lb et = match_count st' lb et"
  by (metis ext)

lemma match_count_balanced_gen:
  assumes "cbit0 c = (b0 \<noteq> sumb lb)" and "cbit1 c = odd (length lb)"
  shows "match_count (spec' h lb b0) lb et =
         (let cet = et @ [c +c sumt et] in
          if length et = h \<and> Color0 \<notin> set cet then gen_dyck (Suc (length lb)) (count_cbit1 cet) else 0)"
  using assms
proof (induction et arbitrary: h c lb b0)
  case Nil
  show ?case
  proof (cases "length lb")
    case 0
    then have lb: "lb = []" by simp
    then have "c = ccons False b0" using Nil.prems ccons_cbits[of c] by simp
    then show ?thesis using lb by (cases b0) (auto simp: spec'_def Let_def gram_balanced_cgram_Nil dyck_def)
  next
    case (Suc d)
    show ?thesis
    proof (cases d)
      case 0
      have c0: "c \<noteq> Color0" using Nil.prems Suc 0 by auto
      have "gen_dyck 2 (Suc 0) = 1" by (simp add: numeral_2_eq_2)
      then show ?thesis using Suc 0 c0 Nil.prems
        by (auto simp: spec'_def Let_def gram_balanced_cgram_Nil numeral_2_eq_2)
    next
      case (Suc d')
      have "gen_dyck (Suc (length lb)) (if cbit1 c then 1 else 0) = 0"
        using gen_dyck_ge3_0[of "Suc (length lb)"] gen_dyck_ge3_1[of "Suc (length lb)"]
          \<open>length lb = Suc d\<close> Suc by simp
      then show ?thesis using \<open>length lb = Suc d\<close> Suc
        by (auto simp: spec'_def Let_def gram_balanced_cgram_Nil)
    qed
  qed
next
  case (Cons e et)
  show ?case
  proof (cases h)
    case 0
    have "match_count (spec' h lb b0) lb (e # et) = 0"
      by (rule match_count_len0) (simp add: spec'_def 0)
    then show ?thesis using 0 by (simp add: Let_def)
  next
    case (Suc h')
    have cet: "(e # et) @ [c +c sumt (e # et)] = e # (et @ [(e +c c) +c sumt et])"
      by (simp add: addcA[symmetric] addcC[of c e])
    show ?thesis
    proof (cases e)
      case Color0
      then show ?thesis using Suc by (simp add: Let_def)
    next
      case Color1
      have st: "spec' h lb b0 (Gskip # w) = spec' h' lb (\<not> b0) w" for w
        using Suc by (simp add: spec'_def)
      have IH: "match_count (spec' h' lb (\<not> b0)) lb et =
                (let cet = et @ [(Color1 +c c) +c sumt et] in
                 if length et = h' \<and> Color0 \<notin> set cet then gen_dyck (Suc (length lb)) (count_cbit1 cet) else 0)"
        using Cons.IH[of "Color1 +c c" "\<not> b0" lb h'] Cons.prems by (simp add: cbit0_addc cbit1_addc)
      show ?thesis using IH st Color1 Suc cet by (simp add: Let_def match_count_cong[OF st])
    next
      case Color2
      have stp: "spec' h lb b0 (Gpush # w) = spec' h' (False # lb) b0 w" for w
        using Suc by (simp add: spec'_def)
      have IHp: "match_count (spec' h' (False # lb) b0) (False # lb) et =
                (let cet = et @ [(Color2 +c c) +c sumt et] in
                 if length et = h' \<and> Color0 \<notin> set cet then gen_dyck (Suc (Suc (length lb))) (count_cbit1 cet) else 0)"
        using Cons.IH[of "Color2 +c c" b0 "False # lb" h'] Cons.prems by (simp add: cbit0_addc cbit1_addc)
      define X where "X = (let cet = et @ [(Color2 +c c) +c sumt et] in length et = h' \<and> Color0 \<notin> set cet)"
      define N where "N = count_cbit1 (et @ [(Color2 +c c) +c sumt et])"
      have pop: "(case lb of [] \<Rightarrow> 0
                  | b # bs' \<Rightarrow> if b then match_count (\<lambda>w. spec' h lb b0 (Gpop1 # w)) bs' et
                              else match_count (\<lambda>w. spec' h lb b0 (Gpop0 # w)) bs' et) =
                 (if X then gen_dyck (length lb) N else 0)"
      proof (cases lb)
        case Nil
        then show ?thesis by (cases N) simp_all
      next
        case (Cons b bs')
        show ?thesis
        proof (cases b)
          case True
          have st: "spec' h lb b0 (Gpop1 # w) = spec' h' bs' (\<not> b0) w" for w
            using Suc Cons by (simp add: spec'_def)
          have "match_count (spec' h' bs' (\<not> b0)) bs' et =
                (if X then gen_dyck (Suc (length bs')) N else 0)"
            using Cons.IH[of "Color2 +c c" "\<not> b0" bs' h'] \<open>cbit0 c = (b0 \<noteq> sumb lb)\<close>
              \<open>cbit1 c = odd (length lb)\<close> Cons True
            by (simp add: cbit0_addc cbit1_addc X_def N_def Let_def)
          then show ?thesis using Cons True match_count_cong[OF st] by simp
        next
          case False
          have st: "spec' h lb b0 (Gpop0 # w) = spec' h' bs' b0 w" for w
            using Suc Cons by (simp add: spec'_def)
          have "match_count (spec' h' bs' b0) bs' et =
                (if X then gen_dyck (Suc (length bs')) N else 0)"
            using Cons.IH[of "Color2 +c c" b0 bs' h'] \<open>cbit0 c = (b0 \<noteq> sumb lb)\<close>
              \<open>cbit1 c = odd (length lb)\<close> Cons False
            by (simp add: cbit0_addc cbit1_addc X_def N_def Let_def)
          then show ?thesis using Cons False match_count_cong[OF st] by simp
        qed
      qed
      have "match_count (spec' h lb b0) lb (e # et) =
            match_count (spec' h' (False # lb) b0) (False # lb) et + (if X then gen_dyck (length lb) N else 0)"
        using Color2 pop match_count_cong[OF stp] by simp
      also have "\<dots> = (if X then gen_dyck (Suc (Suc (length lb))) N + gen_dyck (length lb) N else 0)"
        using IHp by (simp add: X_def N_def Let_def)
      also have "\<dots> = (if X then gen_dyck (Suc (length lb)) (Suc N) else 0)"
      proof (cases "length lb")
        case 0
        then show ?thesis by (cases N) simp_all
      next
        case (Suc k)
        then show ?thesis by simp
      qed
      finally show ?thesis using Color2 Suc cet by (simp add: X_def N_def Let_def)
    next
      case Color3
      have stp: "spec' h lb b0 (Gpush # w) = spec' h' (True # lb) b0 w" for w
        using Suc by (simp add: spec'_def)
      have IHp: "match_count (spec' h' (True # lb) b0) (True # lb) et =
                (let cet = et @ [(Color3 +c c) +c sumt et] in
                 if length et = h' \<and> Color0 \<notin> set cet then gen_dyck (Suc (Suc (length lb))) (count_cbit1 cet) else 0)"
        using Cons.IH[of "Color3 +c c" b0 "True # lb" h'] Cons.prems by (simp add: cbit0_addc cbit1_addc)
      define X where "X = (let cet = et @ [(Color3 +c c) +c sumt et] in length et = h' \<and> Color0 \<notin> set cet)"
      define N where "N = count_cbit1 (et @ [(Color3 +c c) +c sumt et])"
      have pop: "(case lb of [] \<Rightarrow> 0
                  | b # bs' \<Rightarrow> if b then match_count (\<lambda>w. spec' h lb b0 (Gpop0 # w)) bs' et
                              else match_count (\<lambda>w. spec' h lb b0 (Gpop1 # w)) bs' et) =
                 (if X then gen_dyck (length lb) N else 0)"
      proof (cases lb)
        case Nil
        then show ?thesis by (cases N) simp_all
      next
        case (Cons b bs')
        show ?thesis
        proof (cases b)
          case True
          have st: "spec' h lb b0 (Gpop0 # w) = spec' h' bs' b0 w" for w
            using Suc Cons by (simp add: spec'_def)
          have "match_count (spec' h' bs' b0) bs' et =
                (if X then gen_dyck (Suc (length bs')) N else 0)"
            using Cons.IH[of "Color3 +c c" b0 bs' h'] \<open>cbit0 c = (b0 \<noteq> sumb lb)\<close>
              \<open>cbit1 c = odd (length lb)\<close> Cons True
            by (simp add: cbit0_addc cbit1_addc X_def N_def Let_def)
          then show ?thesis using Cons True match_count_cong[OF st] by simp
        next
          case False
          have st: "spec' h lb b0 (Gpop1 # w) = spec' h' bs' (\<not> b0) w" for w
            using Suc Cons by (simp add: spec'_def)
          have "match_count (spec' h' bs' (\<not> b0)) bs' et =
                (if X then gen_dyck (Suc (length bs')) N else 0)"
            using Cons.IH[of "Color3 +c c" "\<not> b0" bs' h'] \<open>cbit0 c = (b0 \<noteq> sumb lb)\<close>
              \<open>cbit1 c = odd (length lb)\<close> Cons False
            by (simp add: cbit0_addc cbit1_addc X_def N_def Let_def)
          then show ?thesis using Cons False match_count_cong[OF st] by simp
        qed
      qed
      have "match_count (spec' h lb b0) lb (e # et) =
            match_count (spec' h' (True # lb) b0) (True # lb) et + (if X then gen_dyck (length lb) N else 0)"
        using Color3 pop match_count_cong[OF stp] by simp
      also have "\<dots> = (if X then gen_dyck (Suc (Suc (length lb))) N + gen_dyck (length lb) N else 0)"
        using IHp by (simp add: X_def N_def Let_def)
      also have "\<dots> = (if X then gen_dyck (Suc (length lb)) (Suc N) else 0)"
      proof (cases "length lb")
        case 0
        then show ?thesis by (cases N) simp_all
      next
        case (Suc k)
        then show ?thesis by simp
      qed
      finally show ?thesis using Color3 Suc cet by (simp add: X_def N_def Let_def)
    qed
  qed
qed

lemma match_count_balanced:
  "match_count (init_gtree_spec h) [] et =
     (if length et = h \<and> Color0 \<notin> set (ctrace et) then dyck (count_cbit1 (ctrace et)) else 0)"
proof -
  have "init_gtree_spec h = spec' h [] False" by (simp add: fun_eq_iff init_gtree_spec_def spec'_def)
  then show ?thesis using match_count_balanced_gen[of Color0 False "[]" h et]
    by (simp add: ctrace_def dyck_def Let_def)
qed

section \<open>Correctness of the initial tree\<close>

lemma gtree_mem_empty4 [simp]: "\<not> gtree_mem (GtreeNode GtreeEmpty GtreeEmpty GtreeEmpty GtreeEmpty) w"
  by (cases w) simp_all

definition Lget :: "gtree_table \<Rightarrow> nat \<Rightarrow> gtree_pair" where
  "Lget L j = (if j < length L then L ! j else empty_gtree_pair)"

lemma Lget_Cons [simp]: "Lget (x # L) (Suc j) = Lget L j"
  by (simp add: Lget_def)

lemma gtsub_Cons [simp]: "gtsub (x # L) (Suc j) b = gtsub L j b"
  by (simp add: gtsub_def)

lemma gtsub_merge_line:
  "k \<le> d \<Longrightarrow>
   gtree_mem (gtsub (gtree_merge_line pt0 pt1 pt2 lpt d) k b) w =
   gtree_mem (gtree_pair_sub (gtree_merge_pairs (Lget (pt2 # pt1 # pt0 # lpt) (k + 2))
               (Lget (pt2 # pt1 # pt0 # lpt) (k + 1)) (Lget (pt2 # pt1 # pt0 # lpt) k)) b) w"
proof (induction pt0 pt1 pt2 lpt d arbitrary: k rule: gtree_merge_line.induct)
  case (1 pt0 pt1 pt2 lpt)
  then show ?case by (simp add: gtsub_def Lget_def)
next
  case (2 pt0 pt1 pt2 d)
  have E: "gtree_mem (gtree_pair_sub (gtree_merge_pairs empty_gtree_pair empty_gtree_pair empty_gtree_pair) b) w = False"
    by (cases b) (simp_all add: empty_gtree_pair_def)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by (simp add: gtsub_def Lget_def)
  next
    case (Suc k')
    show ?thesis
    proof (cases k')
      case 0
      then show ?thesis using Suc by (simp add: gtsub_def Lget_def)
    next
      case (Suc k'')
      show ?thesis
      proof (cases k'')
        case 0
        then show ?thesis using Suc \<open>k = Suc k'\<close> by (simp add: gtsub_def Lget_def)
      next
        case (Suc k3)
        then show ?thesis using \<open>k = Suc k'\<close> \<open>k' = Suc k''\<close> E by (simp add: gtsub_def Lget_def)
      qed
    qed
  qed
next
  case (3 pt0 pt1 pt2 pt lpt d)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by (simp add: gtsub_def Lget_def)
  next
    case (Suc k')
    then have "k' \<le> d" using 3(2) by simp
    then have "gtree_mem (gtsub (gtree_merge_line pt pt0 pt1 lpt d) k' b) w =
               gtree_mem (gtree_pair_sub (gtree_merge_pairs (Lget (pt1 # pt0 # pt # lpt) (k' + 2))
               (Lget (pt1 # pt0 # pt # lpt) (k' + 1)) (Lget (pt1 # pt0 # pt # lpt) k')) b) w"
      by (rule 3(1))
    moreover have "Suc k' + 2 = Suc (k' + 2)" "Suc k' + 1 = Suc (k' + 1)" by simp_all
    ultimately show ?thesis using Suc by (simp only: gtree_merge_line.simps gtsub_Cons Lget_Cons)
  qed
qed

lemma length_merge_line: "length (gtree_merge_line pt0 pt1 pt2 lpt d) \<ge> Suc (min d 1)"
  by (induction pt0 pt1 pt2 lpt d rule: gtree_merge_line.induct) auto

lemma gtree_init_table_spec:
  "(if d = 0 then 0 else 1) < length (gtree_init_table d h) \<and>
   (\<forall>dw bw w. dw \<le> d \<longrightarrow>
      gtree_mem (gtsub (gtree_init_table d h) dw bw) w =
      (length w = Suc h \<and> gram_balanced dw bw (cgram dw bw w)))"
proof (induction h arbitrary: d)
  case 0
  have leaf1: "gtree_mem (gtree_pair_sub (init_gtree_h1 ! k) b) w \<Longrightarrow> length w = Suc 0"
    if "k < 3" for k b w
    using that by (cases k; cases "k - 1"; cases b; cases w; cases "tl w") (auto simp: init_gtree_h1_def)
  have big: "\<not> gram_balanced (Suc (Suc (Suc k))) bw (cgram (Suc (Suc (Suc k))) bw [s])" for k bw s
    by (cases s; cases bw) simp_all
  have "gtree_mem (gtsub init_gtree_h1 dw bw) w = (length w = Suc 0 \<and> gram_balanced dw bw (cgram dw bw w))"
    for dw bw w
  proof (cases "length w = Suc 0")
    case False
    then show ?thesis using leaf1[of dw bw w] by (auto simp: gtsub_def init_gtree_h1_def)
  next
    case True
    then obtain s where w: "w = [s]" by (cases w) auto
    consider "dw = 0" | "dw = 1" | "dw = 2" | k where "dw = Suc (Suc (Suc k))"
      by (metis One_nat_def Suc_1 not0_implies_Suc)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using w by (cases s; cases bw) (simp_all add: gtsub_def init_gtree_h1_def)
    next
      case 2
      then show ?thesis using w by (cases s; cases bw) (simp_all add: gtsub_def init_gtree_h1_def)
    next
      case 3
      then show ?thesis using w by (cases s; cases bw) (simp_all add: gtsub_def init_gtree_h1_def numeral_2_eq_2)
    next
      case 4
      then show ?thesis using w big by (simp add: gtsub_def init_gtree_h1_def)
    qed
  qed
  then show ?case by (simp add: init_gtree_h1_def)
next
  case (Suc h)
  obtain pt1 pt0 lpt where tab: "gtree_init_table (Suc d) h = pt1 # pt0 # lpt"
    using Suc.IH[of "Suc d"] by (cases "gtree_init_table (Suc d) h" rule: remdups_adj.cases) auto
  have IH: "\<And>dw bw w. dw \<le> Suc d \<Longrightarrow> gtree_mem (gtsub (pt1 # pt0 # lpt) dw bw) w =
                (length w = Suc h \<and> gram_balanced dw bw (cgram dw bw w))"
    using Suc.IH[of "Suc d"] tab by simp
  have new: "gtree_init_table d (Suc h) = gtree_merge_line pt0 pt1 empty_gtree_pair lpt d"
    using tab by simp
  define L where "L = empty_gtree_pair # pt1 # pt0 # lpt"
  have Lsub: "gtree_mem (gtree_pair_sub (Lget L (Suc j)) b) w = gtree_mem (gtsub (pt1 # pt0 # lpt) j b) w"
    for j b w by (cases b) (simp_all add: Lget_def L_def gtsub_def empty_gtree_pair_def)
  have L0: "gtree_mem (gtree_pair_sub (Lget L 0) b) w = False" for b w
    by (cases b) (simp_all add: Lget_def L_def empty_gtree_pair_def)
  have ent: "gtree_mem (gtsub (gtree_init_table d (Suc h)) dw bw) w =
             (length w = Suc (Suc h) \<and> gram_balanced dw bw (cgram dw bw w))" if dw: "dw \<le> d" for dw bw w
  proof -
    have m: "gtree_mem (gtsub (gtree_init_table d (Suc h)) dw bw) w =
             gtree_mem (gtree_pair_sub (gtree_merge_pairs (Lget L (dw + 2)) (Lget L (dw + 1)) (Lget L dw)) bw) w"
      using gtsub_merge_line[of dw d pt0 pt1 empty_gtree_pair lpt bw w, OF dw] new by (simp add: L_def)
    obtain a0 a0' where A0: "Lget L (dw + 2) = GtreePair a0 a0'" by (cases "Lget L (dw + 2)") auto
    obtain a1 a1' where A1: "Lget L (dw + 1) = GtreePair a1 a1'" by (cases "Lget L (dw + 1)") auto
    obtain a2 a3 where A2: "Lget L dw = GtreePair a2 a3" by (cases "Lget L dw") auto
    have g0: "gtree_mem a0 v = gtree_mem (gtsub (pt1 # pt0 # lpt) (Suc dw) False) v"
      and g0': "gtree_mem a0' v = gtree_mem (gtsub (pt1 # pt0 # lpt) (Suc dw) True) v"
      and g1: "gtree_mem a1 v = gtree_mem (gtsub (pt1 # pt0 # lpt) dw False) v"
      and g1': "gtree_mem a1' v = gtree_mem (gtsub (pt1 # pt0 # lpt) dw True) v" for v
      using Lsub[of "Suc dw" False v] Lsub[of "Suc dw" True v] Lsub[of dw False v] Lsub[of dw True v] A0 A1
      by simp_all
    have g2: "gtree_mem a2 v = (if dw = 0 then False else gtree_mem (gtsub (pt1 # pt0 # lpt) (dw - 1) False) v)"
      and g3: "gtree_mem a3 v = (if dw = 0 then False else gtree_mem (gtsub (pt1 # pt0 # lpt) (dw - 1) True) v)" for v
      using Lsub[of "dw - 1" False v] Lsub[of "dw - 1" True v] L0[of False v] L0[of True v] A2
      by (cases dw; simp)+
    show ?thesis
    proof (cases w)
      case Nil
      then show ?thesis using m A0 A1 A2 by (cases bw) simp_all
    next
      case (Cons s w')
      have dw1: "Suc dw \<le> Suc d" "dw \<le> Suc d" "dw - 1 \<le> Suc d" using dw by simp_all
      show ?thesis
        using m A0 A1 A2 Cons g0 g0' g1 g1' g2 g3 IH[OF dw1(1)] IH[OF dw1(2)] IH[OF dw1(3)]
        by (cases bw; cases s; cases dw) simp_all
    qed
  qed
  have len: "(if d = 0 then 0 else 1) < length (gtree_init_table d (Suc h))"
    using length_merge_line[of d pt0 pt1 empty_gtree_pair lpt] new by (cases d) auto
  show ?case using len ent by blast
qed

lemma gtree_mem_init_tree: "gtree_mem (gtree_init_tree h) w = init_gtree_spec h w"
proof (cases h)
  case 0
  then show ?thesis by (cases w) (simp_all add: gtree_init_tree_def init_gtree_spec_def)
next
  case (Suc h')
  have sp: "0 < length (gtree_init_table 0 h')"
    "gtree_mem (gtsub (gtree_init_table 0 h') 0 False) w = (length w = Suc h' \<and> gram_balanced 0 False (cgram 0 False w))"
    using gtree_init_table_spec[of 0 h'] by auto
  obtain pt rest where tb: "gtree_init_table 0 h' = pt # rest" using sp(1) by (cases "gtree_init_table 0 h'") auto
  obtain t t' where pt: "pt = GtreePair t t'" by (cases pt) auto
  show ?thesis using Suc sp(2) tb pt by (simp add: gtree_init_tree_def gtsub_def init_gtree_spec_def)
qed

end
