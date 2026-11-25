(* Proof-integrity checkpoint for the real-plane port. *)
theory Plane_Port_Audit
  imports Adjacency_Boxes Scaled_Matte Matte_Extension
begin

ML \<open>
val plane_port_theorems =
  [@{thm rp_compactness_extension}, @{thm rp_exists_adjbox},
   @{thm refine_matte_valid}, @{thm point_matte_in_open},
   @{thm in_extension}, @{thm matte_extension_trans}, @{thm mring_equad},
   @{thm ext1_matte}, @{thm ext1_extends_in}];
val _ = if Thm_Deps.has_skip_proof plane_port_theorems
  then error "The real-plane port depends on a skipped proof" else ();
val _ = if null (Thm_Deps.all_oracles plane_port_theorems)
  then writeln "Real-plane port audit: no skipped proof and no oracle dependencies"
  else error "Unexpected oracle dependency in the real-plane port";
\<close>

end
