theory GDCX_nc_051
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0816: "gdc_sub None 816"
  by (gdc_eval gdc_nc_0816)

lemma gdc_nc_0817: "gdc_sub None 817"
  by (gdc_eval gdc_nc_0817)

lemma gdc_nc_0818: "gdc_sub None 818"
  by (gdc_eval gdc_nc_0818)

lemma gdc_nc_0819: "gdc_sub None 819"
  by (gdc_eval gdc_nc_0819)

lemma gdc_nc_0820: "gdc_sub None 820"
  by (gdc_eval gdc_nc_0820)

lemma gdc_nc_0821: "gdc_sub None 821"
  by (gdc_eval gdc_nc_0821)

lemma gdc_nc_0822: "gdc_sub None 822"
  by (gdc_eval gdc_nc_0822)

lemma gdc_nc_0823: "gdc_sub None 823"
  by (gdc_eval gdc_nc_0823)

lemma gdc_nc_0824: "gdc_sub None 824"
  by (gdc_eval gdc_nc_0824)

lemma gdc_nc_0825: "gdc_sub None 825"
  by (gdc_eval gdc_nc_0825)

lemma gdc_nc_0826: "gdc_sub None 826"
  by (gdc_eval gdc_nc_0826)

lemma gdc_nc_0827: "gdc_sub None 827"
  by (gdc_eval gdc_nc_0827)

lemma gdc_nc_0828: "gdc_sub None 828"
  by (gdc_eval gdc_nc_0828)

lemma gdc_nc_0829: "gdc_sub None 829"
  by (gdc_eval gdc_nc_0829)

lemma gdc_nc_0830: "gdc_sub None 830"
  by (gdc_eval gdc_nc_0830)

lemma gdc_nc_0831: "gdc_sub None 831"
  by (gdc_eval gdc_nc_0831)

lemma gupt_nc_051: "[816..<832] = [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]"
  by (simp add: upt_rec)

lemma gsec_nc_051: "\<forall>j\<in>{16 * 51..<16 * 51 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 51..<16 * 51 + 16}"
  then have "j \<in> set [816..<832]" unfolding set_upt by simp
  then have "j \<in> set [816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831]" unfolding gupt_nc_051 .
  then show "gdc_sub None j" using gdc_nc_0816 gdc_nc_0817 gdc_nc_0818 gdc_nc_0819 gdc_nc_0820 gdc_nc_0821 gdc_nc_0822 gdc_nc_0823 gdc_nc_0824 gdc_nc_0825 gdc_nc_0826 gdc_nc_0827 gdc_nc_0828 gdc_nc_0829 gdc_nc_0830 gdc_nc_0831
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
