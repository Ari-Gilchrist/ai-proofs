(* Matte contours as simple hypermap rings, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Rings
  imports Grid_Planarity
begin

lemma grid_path_path: "grid_path rel x xs \<longleftrightarrow> path rel x xs"
  by (induction xs arbitrary: x) simp_all

lemma grid_cycle_cycle: "grid_cycle rel xs \<longleftrightarrow> cycle rel xs"
  by (cases xs) (simp_all add: grid_cycle_def cycle_def grid_path_path)

lemma cycle_cong_on:
  fixes rel other :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xs :: "'a list"
  assumes agree: "\<And>a b. a\<in>set xs \<Longrightarrow> b\<in>set xs \<Longrightarrow> rel a b = other a b"
  shows "cycle rel xs=cycle other xs"
proof -
  have pointwise: "rel (xs!i) (xs!(Suc i mod length xs)) =
      other (xs!i) (xs!(Suc i mod length xs))" if i: "i<length xs" for i
  proof (rule agree)
    show "xs!i\<in>set xs" by (rule nth_mem[OF i])
    have positive: "0<length xs" using i by arith
    have "Suc i mod length xs<length xs" by (rule mod_less_divisor[OF positive])
    then show "xs!(Suc i mod length xs)\<in>set xs" by (rule nth_mem)
  qed
  show ?thesis unfolding cycle_nth using pointwise by blast
qed

lemma matte_ring_in_gmgrid:
  assumes valid: "valid_matte m" and sub: "set (mdisk m)\<subseteq>grect_set r"
  shows "set (mring m)\<subseteq>gmgrid r"
proof (rule subsetI)
  fix x assume x: "x\<in>set (mring m)"
  have "halfg x\<in>set (mdisk m)"
    using x by (simp only: in_mring[OF valid] gborder_def mem_Collect_eq; blast)
  then have "halfg x\<in>grect_set r" using sub by blast
  then show "x\<in>gmgrid r" by (simp only: gmgrid_iff; blast)
qed

lemma gmdart_rlink_mrlink:
  assumes a: "a\<in>gmgrid r" and b: "b\<in>gmgrid r"
  shows "rlink (gmdart_map r) a b \<longleftrightarrow> mrlink a b"
proof -
  have edge: "gmedge r a=gedge a" using a by (simp add: gmedge_def)
  have edgeD: "gmedge r a\<in>gmgrid r" using a by (simp add: edge)
  have connection: "fconnect (gmface r) (gmedge r a) b \<longleftrightarrow>
      end0g (gmedge r a)=end0g b" by (rule gmface_fconnect_end0[OF edgeD b])
  show ?thesis using connection by (simp add: rlink_def mrlink_def edge end0g_edge)
qed

lemma gmring_simple:
  assumes valid: "valid_matte m" and sub: "set (mdisk m)\<subseteq>grect_set r"
  shows "simple (gmdart_map r) (mring m)"
proof -
  interpret G: hypermap "gmdart_map r" by (rule hypermap_gmdart_map)
  have ringD: "set (mring m)\<subseteq>gmgrid r" by (rule matte_ring_in_gmgrid[OF valid sub])
  have injend: "inj_on end0g (set (mring m))"
    using mring_simple[OF valid] by (simp add: distinct_map)
  have injcyc: "inj_on (cyc (face (gmdart_map r))) (set (mring m))"
  proof (rule inj_onI)
    fix a b assume a: "a\<in>set (mring m)" and b: "b\<in>set (mring m)"
      and eq: "cyc (face (gmdart_map r)) a=cyc (face (gmdart_map r)) b"
    have aD: "a\<in>darts (gmdart_map r)" and bD: "b\<in>darts (gmdart_map r)"
      using ringD a b by auto
    have connection: "fconnect (face (gmdart_map r)) a b" by (rule iffD1[OF G.F.cyc_eq_iff eq])
    have endpoints: "end0g a=end0g b" using connection gmdart_face_end0[OF aD bD] by blast
    show "a=b" by (rule inj_onD[OF injend endpoints a b])
  qed
  show ?thesis unfolding simple_def
    using injcyc mring_uniq[OF valid] by (simp add: distinct_map)
qed

theorem gmring_scycle:
  assumes valid: "valid_matte m" and sub: "set (mdisk m)\<subseteq>grect_set r"
  shows "scycle (gmdart_map r) (rlink (gmdart_map r)) (mring m)"
proof -
  have ringD: "set (mring m)\<subseteq>gmgrid r" by (rule matte_ring_in_gmgrid[OF valid sub])
  have relations: "rlink (gmdart_map r) a b=mrlink a b"
    if "a\<in>set (mring m)" "b\<in>set (mring m)" for a b
    by (rule gmdart_rlink_mrlink) (use ringD that in blast)+
  have cycle: "cycle mrlink (mring m)" using mring_cycle[OF valid] by (simp only: grid_cycle_cycle)
  have eq: "cycle (rlink (gmdart_map r)) (mring m) = cycle mrlink (mring m)"
    by (rule cycle_cong_on) (rule relations; assumption)
  have "cycle (rlink (gmdart_map r)) (mring m)"
    using eq cycle by blast
  then show ?thesis using gmring_simple[OF valid sub] by (simp add: scycle_def)
qed

end
