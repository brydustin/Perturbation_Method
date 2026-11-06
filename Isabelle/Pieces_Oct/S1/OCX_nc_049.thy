theory OCX_nc_049
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0784: "oc_sub None 784"
  by (oc_eval oc_nc_0784)

lemma oc_nc_0785: "oc_sub None 785"
  by (oc_eval oc_nc_0785)

lemma oc_nc_0786: "oc_sub None 786"
  by (oc_eval oc_nc_0786)

lemma oc_nc_0787: "oc_sub None 787"
  by (oc_eval oc_nc_0787)

lemma oc_nc_0788: "oc_sub None 788"
  by (oc_eval oc_nc_0788)

lemma oc_nc_0789: "oc_sub None 789"
  by (oc_eval oc_nc_0789)

lemma oc_nc_0790: "oc_sub None 790"
  by (oc_eval oc_nc_0790)

lemma oc_nc_0791: "oc_sub None 791"
  by (oc_eval oc_nc_0791)

lemma oc_nc_0792: "oc_sub None 792"
  by (oc_eval oc_nc_0792)

lemma oc_nc_0793: "oc_sub None 793"
  by (oc_eval oc_nc_0793)

lemma oc_nc_0794: "oc_sub None 794"
  by (oc_eval oc_nc_0794)

lemma oc_nc_0795: "oc_sub None 795"
  by (oc_eval oc_nc_0795)

lemma oc_nc_0796: "oc_sub None 796"
  by (oc_eval oc_nc_0796)

lemma oc_nc_0797: "oc_sub None 797"
  by (oc_eval oc_nc_0797)

lemma oc_nc_0798: "oc_sub None 798"
  by (oc_eval oc_nc_0798)

lemma oc_nc_0799: "oc_sub None 799"
  by (oc_eval oc_nc_0799)

lemma upt_nc_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma sec_nc_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding upt_nc_049 .
  then show "oc_sub None j" using oc_nc_0784 oc_nc_0785 oc_nc_0786 oc_nc_0787 oc_nc_0788 oc_nc_0789 oc_nc_0790 oc_nc_0791 oc_nc_0792 oc_nc_0793 oc_nc_0794 oc_nc_0795 oc_nc_0796 oc_nc_0797 oc_nc_0798 oc_nc_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
