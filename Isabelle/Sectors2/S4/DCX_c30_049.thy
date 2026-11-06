theory DCX_c30_049
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0784: "dc_sub dc_b30 784"
  by (dc_eval dc_c30_0784)

lemma dc_c30_0785: "dc_sub dc_b30 785"
  by (dc_eval dc_c30_0785)

lemma dc_c30_0786: "dc_sub dc_b30 786"
  by (dc_eval dc_c30_0786)

lemma dc_c30_0787: "dc_sub dc_b30 787"
  by (dc_eval dc_c30_0787)

lemma dc_c30_0788: "dc_sub dc_b30 788"
  by (dc_eval dc_c30_0788)

lemma dc_c30_0789: "dc_sub dc_b30 789"
  by (dc_eval dc_c30_0789)

lemma dc_c30_0790: "dc_sub dc_b30 790"
  by (dc_eval dc_c30_0790)

lemma dc_c30_0791: "dc_sub dc_b30 791"
  by (dc_eval dc_c30_0791)

lemma dc_c30_0792: "dc_sub dc_b30 792"
  by (dc_eval dc_c30_0792)

lemma dc_c30_0793: "dc_sub dc_b30 793"
  by (dc_eval dc_c30_0793)

lemma dc_c30_0794: "dc_sub dc_b30 794"
  by (dc_eval dc_c30_0794)

lemma dc_c30_0795: "dc_sub dc_b30 795"
  by (dc_eval dc_c30_0795)

lemma dc_c30_0796: "dc_sub dc_b30 796"
  by (dc_eval dc_c30_0796)

lemma dc_c30_0797: "dc_sub dc_b30 797"
  by (dc_eval dc_c30_0797)

lemma dc_c30_0798: "dc_sub dc_b30 798"
  by (dc_eval dc_c30_0798)

lemma dc_c30_0799: "dc_sub dc_b30 799"
  by (dc_eval dc_c30_0799)

lemma upt_c30_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma sec_c30_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding upt_c30_049 .
  then show "dc_sub dc_b30 j" using dc_c30_0784 dc_c30_0785 dc_c30_0786 dc_c30_0787 dc_c30_0788 dc_c30_0789 dc_c30_0790 dc_c30_0791 dc_c30_0792 dc_c30_0793 dc_c30_0794 dc_c30_0795 dc_c30_0796 dc_c30_0797 dc_c30_0798 dc_c30_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
