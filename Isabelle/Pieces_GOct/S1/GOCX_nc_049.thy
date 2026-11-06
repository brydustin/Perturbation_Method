theory GOCX_nc_049
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0784: "goc_sub None 784"
  by (goc_eval goc_nc_0784)

lemma goc_nc_0785: "goc_sub None 785"
  by (goc_eval goc_nc_0785)

lemma goc_nc_0786: "goc_sub None 786"
  by (goc_eval goc_nc_0786)

lemma goc_nc_0787: "goc_sub None 787"
  by (goc_eval goc_nc_0787)

lemma goc_nc_0788: "goc_sub None 788"
  by (goc_eval goc_nc_0788)

lemma goc_nc_0789: "goc_sub None 789"
  by (goc_eval goc_nc_0789)

lemma goc_nc_0790: "goc_sub None 790"
  by (goc_eval goc_nc_0790)

lemma goc_nc_0791: "goc_sub None 791"
  by (goc_eval goc_nc_0791)

lemma goc_nc_0792: "goc_sub None 792"
  by (goc_eval goc_nc_0792)

lemma goc_nc_0793: "goc_sub None 793"
  by (goc_eval goc_nc_0793)

lemma goc_nc_0794: "goc_sub None 794"
  by (goc_eval goc_nc_0794)

lemma goc_nc_0795: "goc_sub None 795"
  by (goc_eval goc_nc_0795)

lemma goc_nc_0796: "goc_sub None 796"
  by (goc_eval goc_nc_0796)

lemma goc_nc_0797: "goc_sub None 797"
  by (goc_eval goc_nc_0797)

lemma goc_nc_0798: "goc_sub None 798"
  by (goc_eval goc_nc_0798)

lemma goc_nc_0799: "goc_sub None 799"
  by (goc_eval goc_nc_0799)

lemma gupt_nc_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma gsec_nc_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding gupt_nc_049 .
  then show "goc_sub None j" using goc_nc_0784 goc_nc_0785 goc_nc_0786 goc_nc_0787 goc_nc_0788 goc_nc_0789 goc_nc_0790 goc_nc_0791 goc_nc_0792 goc_nc_0793 goc_nc_0794 goc_nc_0795 goc_nc_0796 goc_nc_0797 goc_nc_0798 goc_nc_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
