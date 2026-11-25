(* Transfer from cutout vertex colours to touching grid mattes, from gridmap.v.
   Original G. Gonthier et al., CeCILL-B. Isabelle/HOL port: Codex. *)
theory Grid_Colouring
  imports Grid_Cutout
begin

fun grid_colour_index :: "color\<Rightarrow>nat" where
  "grid_colour_index Color0=0"
| "grid_colour_index Color1=1"
| "grid_colour_index Color2=2"
| "grid_colour_index Color3=3"

lemma grid_colour_index_bound: "grid_colour_index c<4"
  by (cases c) simp_all

lemma grid_colour_index_inj: "grid_colour_index c=grid_colour_index d \<longleftrightarrow> c=d"
  by (cases c; cases d) simp_all

lemma (in grid_mattes) cutout_colour_transfer:
  assumes cut: "cutout {..<k} G" and colourable: "graph_four_colorable G"
  shows "\<exists>c::nat\<Rightarrow>nat. (\<forall>i<k. c i<4) \<and>
    (\<forall>i<k. \<forall>j<k. madj (cm i) (cm j) \<longrightarrow> c i\<noteq>c j)"
proof -
  interpret H: hypermap G using cut by (simp add: cutout_def)
  obtain col where col: "graph_coloring G col" using colourable
    by (auto simp: graph_four_colorable_def)
  have nodecol: "col (node G x)=col x" if "x\<in>darts G" for x
    using col that by (auto simp: graph_coloring_def)
  have orbit_colour: "col y=col x" if xD: "x\<in>darts G" and con: "fconnect (node G) x y" for x y
    using con
  proof (induction rule: fconnect_induct)
    case refl show ?case by simp
  next
    case (step z)
    have "z\<in>darts G" using step.hyps xD by (auto simp: fconnect_def)
    then show ?case using nodecol step.IH by simp
  qed
  have same_ring: "col x=col y" if i: "i<k" and x: "x\<in>set (contour i)"
    and y: "y\<in>set (contour i)" for i x y
  proof -
    have cyc: "cycle (frel (node G)) (rev (contour i))" and distinct: "distinct (rev (contour i))"
      using cut i by (simp only: cutout_def ucycle_def; blast)+
    have xr: "x\<in>set (rev (contour i))" using x by simp
    have con: "fconnect (node G) x y"
      using H.N.fcycle_fconnect[OF cyc distinct xr, of y] y by simp
    have xD: "x\<in>darts G" using cut i x by (simp only: cutout_def; blast)
    show ?thesis using orbit_colour[OF xD con] by simp
  qed
  let ?pick = "\<lambda>i. SOME x. x\<in>set (contour i)"
  let ?c = "\<lambda>i. grid_colour_index (col (?pick i))"
  have proper: "?c i\<noteq>?c j" if i: "i<k" and j: "j<k" and adj: "madj (cm i) (cm j)" for i j
  proof -
    obtain d where d: "d\<in>set (contour j)" and ed: "gedge d\<in>set (contour i)"
      using adj by (auto simp: madj_def)
    have picki: "?pick i\<in>set (contour i)"
      by (rule someI[where P="\<lambda>x. x\<in>set (contour i)" and x="gedge d", OF ed])
    have pickj: "?pick j\<in>set (contour j)"
      by (rule someI[where P="\<lambda>x. x\<in>set (contour j)" and x=d, OF d])
    have ci: "col (?pick i)=col (gedge d)" by (rule same_ring[OF i picki ed])
    have cj: "col (?pick j)=col d" by (rule same_ring[OF j pickj d])
    have dD: "d\<in>darts G" using cut j d by (simp only: cutout_def; blast)
    have edge: "edge G d=gedge d" using cut dD by (simp only: cutout_def; blast)
    have different: "col (edge G d)\<noteq>col d"
      using col dD by (auto simp: graph_coloring_def)
    have "col (gedge d)\<noteq>col d" using different by (simp add: edge)
    then show ?thesis by (simp add: grid_colour_index_inj ci cj)
  qed
  show ?thesis by (rule exI[of _ ?c]) (use grid_colour_index_bound proper in blast)
qed

end
