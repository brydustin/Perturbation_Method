theory GOCX_nc_051
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0816: "goc_sub None 816"
  by (goc_eval goc_nc_0816)

lemma goc_nc_0817: "goc_sub None 817"
  by (goc_eval goc_nc_0817)

lemma goc_nc_0818: "goc_sub None 818"
  by (goc_eval goc_nc_0818)

lemma goc_nc_0819: "goc_sub None 819"
  by (goc_eval goc_nc_0819)

lemma goc_nc_0820: "goc_sub None 820"
  by (goc_eval goc_nc_0820)

lemma goc_nc_0821: "goc_sub None 821"
  by (goc_eval goc_nc_0821)

lemma goc_nc_0822: "goc_sub None 822"
  by (goc_eval goc_nc_0822)

lemma goc_nc_0823: "goc_sub None 823"
  by (goc_eval goc_nc_0823)

lemma goc_nc_0824: "goc_sub None 824"
  by (goc_eval goc_nc_0824)

lemma goc_nc_0825: "goc_sub None 825"
  by (goc_eval goc_nc_0825)

lemma goc_nc_0826: "goc_sub None 826"
  by (goc_eval goc_nc_0826)

lemma goc_nc_0827: "goc_sub None 827"
  by (goc_eval goc_nc_0827)

lemma goc_nc_0828: "goc_sub None 828"
  by (goc_eval goc_nc_0828)

lemma goc_nc_0829: "goc_sub None 829"
  by (goc_eval goc_nc_0829)

lemma goc_nc_0830: "goc_sub None 830"
  by (goc_eval goc_nc_0830)

lemma goc_nc_0831: "goc_sub None 831"
  by (goc_eval goc_nc_0831)

lemma gupt_nc_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma gsec_nc_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding gupt_nc_051 .
  then show "goc_sub None j" using goc_nc_0816 goc_nc_0817 goc_nc_0818 goc_nc_0819 goc_nc_0820 goc_nc_0821 goc_nc_0822 goc_nc_0823 goc_nc_0824 goc_nc_0825 goc_nc_0826 goc_nc_0827 goc_nc_0828 goc_nc_0829 goc_nc_0830 goc_nc_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
