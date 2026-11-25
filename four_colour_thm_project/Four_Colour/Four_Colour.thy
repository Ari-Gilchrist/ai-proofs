(* The finite real-plane Four Colour Theorem. *)
theory Four_Colour
  imports Four_Colour_Grid_Hypermap.Grid_Colouring Four_Colour_Grid_Map.Grid_Contact
    Four_Colour_Combinatorial.Combinatorial_Four_Colour
begin

text \<open>The grid construction turns disjoint region mattes into boundary
  cycles of a finite planar loopless hypermap. Its vertex colouring supplies
  four colours for the mattes, preserving every required region adjacency.\<close>

theorem four_colour_grid_mattes:
  assumes cm: "grid_cm_proper k cm"
  shows "\<exists>c::nat\<Rightarrow>nat. (\<forall>i<k. c i<4) \<and>
    (\<forall>i<k. \<forall>j<k. madj (cm i) (cm j) \<longrightarrow> c i\<noteq>c j)"
proof -
  let ?r = "matte_bbox k cm"
  interpret M: grid_mattes ?r k cm
  proof unfold_locales
    show "gr_proper ?r" by (rule matte_bbox_proper)
    show "grid_cm_proper k cm" by (rule cm)
    fix i assume i: "i<k"
    show "set (mdisk (cm i))\<subseteq>grect_set ?r" by (rule matte_bbox_contains[OF i])
  qed
  obtain G where cut: "M.cutout {..<k} G" and hyp: "hypermap G"
    and planar: "planar G" and loopless: "loopless G"
    using M.planar_loopless_cutout by blast
  interpret H: hypermap G by (rule hyp)
  have "graph_four_colorable G" by (rule H.four_colour_graph[OF planar loopless])
  then show ?thesis by (rule M.cutout_colour_transfer[OF cut])
qed

text \<open>The finite real-plane theorem has only the finite simple-map
  hypothesis. The discretization and all combinatorial certificate obligations
  are discharged by the imported development.\<close>

theorem four_color_finite:
  fixes m :: "rp_point region_map"
  assumes finite: "rp_finite_simple_map m"
  shows "rp_colorable_with 4 m"
proof -
  obtain k r cm where repr: "rp_map_repr m k r" and proper: "grid_cm_proper k cm"
    and contact: "\<forall>e\<in>rp_adj_indices m k r. madj (cm (fst e)) (cm (snd e))"
    using rp_exists_touching_grid_mattes[OF finite] by blast
  obtain c :: "nat\<Rightarrow>nat" where palette: "\<forall>i<k. c i<4"
    and colours: "\<forall>i<k. \<forall>j<k. madj (cm i) (cm j) \<longrightarrow> c i\<noteq>c j"
    using four_colour_grid_mattes[OF proper] by blast
  have plain: "rp_plain m" using finite
    by (simp add: rp_finite_simple_map_def rp_simple_map_def)
  show ?thesis by (rule rp_touching_matte_colour_transfer[OF plain repr contact palette])
    (use colours in blast)
qed

text \<open>Colouring compactness removes the finiteness restriction.\<close>

corollary four_color:
  fixes m :: "rp_point region_map"
  assumes "rp_simple_map m"
  shows "rp_colorable_with 4 m"
  by (rule rp_compactness_extension[OF assms four_color_finite])

ML \<open>
val real_plane_four_colour_theorems =
  [@{thm four_color_finite}, @{thm four_color}];
val _ = if Thm_Deps.has_skip_proof real_plane_four_colour_theorems
  then error "The real-plane Four Colour Theorem depends on a skipped proof" else ();
val real_plane_oracles = Thm_Deps.all_oracles real_plane_four_colour_theorems;
val _ = if List.all
    (fn ((name, _), _) => name = \<^verbatim>\<open>Code_Generator.holds_by_evaluation\<close>)
    real_plane_oracles
  then writeln "Real-plane Four Colour audit: no skipped proofs; only code evaluation is allowed"
  else error "Unexpected oracle in the real-plane Four Colour Theorem";
\<close>

end
