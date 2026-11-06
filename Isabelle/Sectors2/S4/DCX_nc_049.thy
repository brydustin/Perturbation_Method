theory DCX_nc_049
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0784: "dc_sub None 784"
  by (dc_eval dc_nc_0784)

lemma dc_nc_0785: "dc_sub None 785"
  by (dc_eval dc_nc_0785)

lemma dc_nc_0786: "dc_sub None 786"
  by (dc_eval dc_nc_0786)

lemma dc_nc_0787: "dc_sub None 787"
  by (dc_eval dc_nc_0787)

lemma dc_nc_0788: "dc_sub None 788"
  by (dc_eval dc_nc_0788)

lemma dc_nc_0789: "dc_sub None 789"
  by (dc_eval dc_nc_0789)

lemma dc_nc_0790: "dc_sub None 790"
  by (dc_eval dc_nc_0790)

lemma dc_nc_0791: "dc_sub None 791"
  by (dc_eval dc_nc_0791)

lemma dc_nc_0792: "dc_sub None 792"
  by (dc_eval dc_nc_0792)

lemma dc_nc_0793: "dc_sub None 793"
  by (dc_eval dc_nc_0793)

lemma dc_nc_0794: "dc_sub None 794"
  by (dc_eval dc_nc_0794)

lemma dc_nc_0795: "dc_sub None 795"
  by (dc_eval dc_nc_0795)

lemma dc_nc_0796: "dc_sub None 796"
  by (dc_eval dc_nc_0796)

lemma dc_nc_0797: "dc_sub None 797"
  by (dc_eval dc_nc_0797)

lemma dc_nc_0798: "dc_sub None 798"
  by (dc_eval dc_nc_0798)

lemma dc_nc_0799: "dc_sub None 799"
  by (dc_eval dc_nc_0799)

lemma upt_nc_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma sec_nc_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding upt_nc_049 .
  then show "dc_sub None j" using dc_nc_0784 dc_nc_0785 dc_nc_0786 dc_nc_0787 dc_nc_0788 dc_nc_0789 dc_nc_0790 dc_nc_0791 dc_nc_0792 dc_nc_0793 dc_nc_0794 dc_nc_0795 dc_nc_0796 dc_nc_0797 dc_nc_0798 dc_nc_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
