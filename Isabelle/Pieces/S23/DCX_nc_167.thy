theory DCX_nc_167
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2672: "dc_sub None 2672"
  by (dc_eval dc_nc_2672)

lemma dc_nc_2673: "dc_sub None 2673"
  by (dc_eval dc_nc_2673)

lemma dc_nc_2674: "dc_sub None 2674"
  by (dc_eval dc_nc_2674)

lemma dc_nc_2675: "dc_sub None 2675"
  by (dc_eval dc_nc_2675)

lemma dc_nc_2676: "dc_sub None 2676"
  by (dc_eval dc_nc_2676)

lemma dc_nc_2677: "dc_sub None 2677"
  by (dc_eval dc_nc_2677)

lemma dc_nc_2678: "dc_sub None 2678"
  by (dc_eval dc_nc_2678)

lemma dc_nc_2679: "dc_sub None 2679"
  by (dc_eval dc_nc_2679)

lemma dc_nc_2680: "dc_sub None 2680"
  by (dc_eval dc_nc_2680)

lemma dc_nc_2681: "dc_sub None 2681"
  by (dc_eval dc_nc_2681)

lemma dc_nc_2682: "dc_sub None 2682"
  by (dc_eval dc_nc_2682)

lemma dc_nc_2683: "dc_sub None 2683"
  by (dc_eval dc_nc_2683)

lemma dc_nc_2684: "dc_sub None 2684"
  by (dc_eval dc_nc_2684)

lemma dc_nc_2685: "dc_sub None 2685"
  by (dc_eval dc_nc_2685)

lemma dc_nc_2686: "dc_sub None 2686"
  by (dc_eval dc_nc_2686)

lemma dc_nc_2687: "dc_sub None 2687"
  by (dc_eval dc_nc_2687)

lemma upt_nc_167: "[2672..<2688] = [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]"
  by (simp add: upt_rec)

lemma sec_nc_167: "\<forall>j\<in>{16 * 167..<16 * 167 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 167..<16 * 167 + 16}"
  then have "j \<in> set [2672..<2688]" unfolding set_upt by simp
  then have "j \<in> set [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]" unfolding upt_nc_167 .
  then show "dc_sub None j" using dc_nc_2672 dc_nc_2673 dc_nc_2674 dc_nc_2675 dc_nc_2676 dc_nc_2677 dc_nc_2678 dc_nc_2679 dc_nc_2680 dc_nc_2681 dc_nc_2682 dc_nc_2683 dc_nc_2684 dc_nc_2685 dc_nc_2686 dc_nc_2687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
