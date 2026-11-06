theory DCX_c30_167
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2672: "dc_sub dc_b30 2672"
  by (dc_eval dc_c30_2672)

lemma dc_c30_2673: "dc_sub dc_b30 2673"
  by (dc_eval dc_c30_2673)

lemma dc_c30_2674: "dc_sub dc_b30 2674"
  by (dc_eval dc_c30_2674)

lemma dc_c30_2675: "dc_sub dc_b30 2675"
  by (dc_eval dc_c30_2675)

lemma dc_c30_2676: "dc_sub dc_b30 2676"
  by (dc_eval dc_c30_2676)

lemma dc_c30_2677: "dc_sub dc_b30 2677"
  by (dc_eval dc_c30_2677)

lemma dc_c30_2678: "dc_sub dc_b30 2678"
  by (dc_eval dc_c30_2678)

lemma dc_c30_2679: "dc_sub dc_b30 2679"
  by (dc_eval dc_c30_2679)

lemma dc_c30_2680: "dc_sub dc_b30 2680"
  by (dc_eval dc_c30_2680)

lemma dc_c30_2681: "dc_sub dc_b30 2681"
  by (dc_eval dc_c30_2681)

lemma dc_c30_2682: "dc_sub dc_b30 2682"
  by (dc_eval dc_c30_2682)

lemma dc_c30_2683: "dc_sub dc_b30 2683"
  by (dc_eval dc_c30_2683)

lemma dc_c30_2684: "dc_sub dc_b30 2684"
  by (dc_eval dc_c30_2684)

lemma dc_c30_2685: "dc_sub dc_b30 2685"
  by (dc_eval dc_c30_2685)

lemma dc_c30_2686: "dc_sub dc_b30 2686"
  by (dc_eval dc_c30_2686)

lemma dc_c30_2687: "dc_sub dc_b30 2687"
  by (dc_eval dc_c30_2687)

lemma upt_c30_167: "[2672..<2688] = [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]"
  by (simp add: upt_rec)

lemma sec_c30_167: "\<forall>j\<in>{16 * 167..<16 * 167 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 167..<16 * 167 + 16}"
  then have "j \<in> set [2672..<2688]" unfolding set_upt by simp
  then have "j \<in> set [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]" unfolding upt_c30_167 .
  then show "dc_sub dc_b30 j" using dc_c30_2672 dc_c30_2673 dc_c30_2674 dc_c30_2675 dc_c30_2676 dc_c30_2677 dc_c30_2678 dc_c30_2679 dc_c30_2680 dc_c30_2681 dc_c30_2682 dc_c30_2683 dc_c30_2684 dc_c30_2685 dc_c30_2686 dc_c30_2687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
