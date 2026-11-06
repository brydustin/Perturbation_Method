theory GOCX_nc_167
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2672: "goc_sub None 2672"
  by (goc_eval goc_nc_2672)

lemma goc_nc_2673: "goc_sub None 2673"
  by (goc_eval goc_nc_2673)

lemma goc_nc_2674: "goc_sub None 2674"
  by (goc_eval goc_nc_2674)

lemma goc_nc_2675: "goc_sub None 2675"
  by (goc_eval goc_nc_2675)

lemma goc_nc_2676: "goc_sub None 2676"
  by (goc_eval goc_nc_2676)

lemma goc_nc_2677: "goc_sub None 2677"
  by (goc_eval goc_nc_2677)

lemma goc_nc_2678: "goc_sub None 2678"
  by (goc_eval goc_nc_2678)

lemma goc_nc_2679: "goc_sub None 2679"
  by (goc_eval goc_nc_2679)

lemma goc_nc_2680: "goc_sub None 2680"
  by (goc_eval goc_nc_2680)

lemma goc_nc_2681: "goc_sub None 2681"
  by (goc_eval goc_nc_2681)

lemma goc_nc_2682: "goc_sub None 2682"
  by (goc_eval goc_nc_2682)

lemma goc_nc_2683: "goc_sub None 2683"
  by (goc_eval goc_nc_2683)

lemma goc_nc_2684: "goc_sub None 2684"
  by (goc_eval goc_nc_2684)

lemma goc_nc_2685: "goc_sub None 2685"
  by (goc_eval goc_nc_2685)

lemma goc_nc_2686: "goc_sub None 2686"
  by (goc_eval goc_nc_2686)

lemma goc_nc_2687: "goc_sub None 2687"
  by (goc_eval goc_nc_2687)

lemma gupt_nc_167: "[2672..<2688] = [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]"
  by (simp add: upt_rec)

lemma gsec_nc_167: "\<forall>j\<in>{16 * 167..<16 * 167 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 167..<16 * 167 + 16}"
  then have "j \<in> set [2672..<2688]" unfolding set_upt by simp
  then have "j \<in> set [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]" unfolding gupt_nc_167 .
  then show "goc_sub None j" using goc_nc_2672 goc_nc_2673 goc_nc_2674 goc_nc_2675 goc_nc_2676 goc_nc_2677 goc_nc_2678 goc_nc_2679 goc_nc_2680 goc_nc_2681 goc_nc_2682 goc_nc_2683 goc_nc_2684 goc_nc_2685 goc_nc_2686 goc_nc_2687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
