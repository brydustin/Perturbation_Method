theory GDCX_nc_049
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0784: "gdc_sub None 784"
  by (gdc_eval gdc_nc_0784)

lemma gdc_nc_0785: "gdc_sub None 785"
  by (gdc_eval gdc_nc_0785)

lemma gdc_nc_0786: "gdc_sub None 786"
  by (gdc_eval gdc_nc_0786)

lemma gdc_nc_0787: "gdc_sub None 787"
  by (gdc_eval gdc_nc_0787)

lemma gdc_nc_0788: "gdc_sub None 788"
  by (gdc_eval gdc_nc_0788)

lemma gdc_nc_0789: "gdc_sub None 789"
  by (gdc_eval gdc_nc_0789)

lemma gdc_nc_0790: "gdc_sub None 790"
  by (gdc_eval gdc_nc_0790)

lemma gdc_nc_0791: "gdc_sub None 791"
  by (gdc_eval gdc_nc_0791)

lemma gdc_nc_0792: "gdc_sub None 792"
  by (gdc_eval gdc_nc_0792)

lemma gdc_nc_0793: "gdc_sub None 793"
  by (gdc_eval gdc_nc_0793)

lemma gdc_nc_0794: "gdc_sub None 794"
  by (gdc_eval gdc_nc_0794)

lemma gdc_nc_0795: "gdc_sub None 795"
  by (gdc_eval gdc_nc_0795)

lemma gdc_nc_0796: "gdc_sub None 796"
  by (gdc_eval gdc_nc_0796)

lemma gdc_nc_0797: "gdc_sub None 797"
  by (gdc_eval gdc_nc_0797)

lemma gdc_nc_0798: "gdc_sub None 798"
  by (gdc_eval gdc_nc_0798)

lemma gdc_nc_0799: "gdc_sub None 799"
  by (gdc_eval gdc_nc_0799)

lemma gupt_nc_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma gsec_nc_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding gupt_nc_049 .
  then show "gdc_sub None j" using gdc_nc_0784 gdc_nc_0785 gdc_nc_0786 gdc_nc_0787 gdc_nc_0788 gdc_nc_0789 gdc_nc_0790 gdc_nc_0791 gdc_nc_0792 gdc_nc_0793 gdc_nc_0794 gdc_nc_0795 gdc_nc_0796 gdc_nc_0797 gdc_nc_0798 gdc_nc_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
