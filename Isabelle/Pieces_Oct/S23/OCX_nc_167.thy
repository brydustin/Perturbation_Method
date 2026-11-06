theory OCX_nc_167
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2672: "oc_sub None 2672"
  by (oc_eval oc_nc_2672)

lemma oc_nc_2673: "oc_sub None 2673"
  by (oc_eval oc_nc_2673)

lemma oc_nc_2674: "oc_sub None 2674"
  by (oc_eval oc_nc_2674)

lemma oc_nc_2675: "oc_sub None 2675"
  by (oc_eval oc_nc_2675)

lemma oc_nc_2676: "oc_sub None 2676"
  by (oc_eval oc_nc_2676)

lemma oc_nc_2677: "oc_sub None 2677"
  by (oc_eval oc_nc_2677)

lemma oc_nc_2678: "oc_sub None 2678"
  by (oc_eval oc_nc_2678)

lemma oc_nc_2679: "oc_sub None 2679"
  by (oc_eval oc_nc_2679)

lemma oc_nc_2680: "oc_sub None 2680"
  by (oc_eval oc_nc_2680)

lemma oc_nc_2681: "oc_sub None 2681"
  by (oc_eval oc_nc_2681)

lemma oc_nc_2682: "oc_sub None 2682"
  by (oc_eval oc_nc_2682)

lemma oc_nc_2683: "oc_sub None 2683"
  by (oc_eval oc_nc_2683)

lemma oc_nc_2684: "oc_sub None 2684"
  by (oc_eval oc_nc_2684)

lemma oc_nc_2685: "oc_sub None 2685"
  by (oc_eval oc_nc_2685)

lemma oc_nc_2686: "oc_sub None 2686"
  by (oc_eval oc_nc_2686)

lemma oc_nc_2687: "oc_sub None 2687"
  by (oc_eval oc_nc_2687)

lemma upt_nc_167: "[2672..<2688] = [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]"
  by (simp add: upt_rec)

lemma sec_nc_167: "\<forall>j\<in>{16 * 167..<16 * 167 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 167..<16 * 167 + 16}"
  then have "j \<in> set [2672..<2688]" unfolding set_upt by simp
  then have "j \<in> set [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]" unfolding upt_nc_167 .
  then show "oc_sub None j" using oc_nc_2672 oc_nc_2673 oc_nc_2674 oc_nc_2675 oc_nc_2676 oc_nc_2677 oc_nc_2678 oc_nc_2679 oc_nc_2680 oc_nc_2681 oc_nc_2682 oc_nc_2683 oc_nc_2684 oc_nc_2685 oc_nc_2686 oc_nc_2687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
