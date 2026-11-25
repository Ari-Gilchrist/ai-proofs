(* Proof-integrity checkpoint for the finite-grid construction. *)
theory Grid_Port_Audit
  imports Grid_Bounds Grid_Contact
begin

ML \<open>
val grid_port_theorems =
  [@{thm madj_monotone_disjoint}, @{thm coarse_in_unchanged_refine},
   @{thm grid_cm_replace_proper}, @{thm grid_adjacency_preserved_update},
   @{thm grid_adj_pending_update}, @{thm matte_bbox_contains},
   @{thm matte_bbox_proper}, @{thm finite_gmgrid}, @{thm gmgrid_edge},
   @{thm grid_extend_adj}, @{thm rp_exists_touching_grid_mattes},
   @{thm rp_touching_matte_colour_transfer}];
val _ = if Thm_Deps.has_skip_proof grid_port_theorems
  then error "The grid port depends on a skipped proof" else ();
val _ = if null (Thm_Deps.all_oracles grid_port_theorems)
  then writeln "Grid port audit: no skipped proof and no oracle dependencies"
  else error "Unexpected oracle dependency in the grid port";
\<close>

end
