(* Proof-integrity checkpoint for the matte-extension port. *)
theory Matte_Port_Audit
  imports Plane_Discretization_Data
begin

ML \<open>
val matte_port_theorems =
  [@{thm ext2_matte}, @{thm matte_extension_ext2},
   @{thm matte_extension_first_contact}, @{thm coarse_extends_in},
   @{thm extend_madj}, @{thm mcorner0}, @{thm refine_mcorner},
   @{thm connected_matte}, @{thm rp_exists_smatte}, @{thm common_matte_box_scale},
   @{thm rp_exists_grid_data}];
val _ = if Thm_Deps.has_skip_proof matte_port_theorems
  then error "The matte port depends on a skipped proof" else ();
val _ = if null (Thm_Deps.all_oracles matte_port_theorems)
  then writeln "Matte port audit: no skipped proof and no oracle dependencies"
  else error "Unexpected oracle dependency in the matte port";
\<close>

end
