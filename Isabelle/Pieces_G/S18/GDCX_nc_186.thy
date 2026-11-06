theory GDCX_nc_186
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2976: "gdc_sub None 2976"
  by (gdc_eval gdc_nc_2976)

lemma gdc_nc_2977: "gdc_sub None 2977"
  by (gdc_eval gdc_nc_2977)

lemma gdc_nc_2978: "gdc_sub None 2978"
  by (gdc_eval gdc_nc_2978)

lemma gdc_nc_2979: "gdc_sub None 2979"
  by (gdc_eval gdc_nc_2979)

lemma gdc_nc_2980: "gdc_sub None 2980"
  by (gdc_eval gdc_nc_2980)

lemma gdc_nc_2981: "gdc_sub None 2981"
  by (gdc_eval gdc_nc_2981)

lemma gdc_nc_2982: "gdc_sub None 2982"
  by (gdc_eval gdc_nc_2982)

lemma gdc_nc_2983: "gdc_sub None 2983"
  by (gdc_eval gdc_nc_2983)

lemma gdc_nc_2984: "gdc_sub None 2984"
  by (gdc_eval gdc_nc_2984)

lemma gdc_nc_2985: "gdc_sub None 2985"
  by (gdc_eval gdc_nc_2985)

lemma gdc_nc_2986: "gdc_sub None 2986"
  by (gdc_eval gdc_nc_2986)

lemma gdc_nc_2987: "gdc_sub None 2987"
  by (gdc_eval gdc_nc_2987)

lemma gdc_nc_2988: "gdc_sub None 2988"
  by (gdc_eval gdc_nc_2988)

lemma gdc_nc_2989: "gdc_sub None 2989"
  by (gdc_eval gdc_nc_2989)

lemma gdc_nc_2990: "gdc_sub None 2990"
  by (gdc_eval gdc_nc_2990)

lemma gdc_nc_2991: "gdc_sub None 2991"
  by (gdc_eval gdc_nc_2991)

lemma gupt_nc_186: "[2976..<2992] = [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]"
  by (simp add: upt_rec)

lemma gsec_nc_186: "\<forall>j\<in>{16 * 186..<16 * 186 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 186..<16 * 186 + 16}"
  then have "j \<in> set [2976..<2992]" unfolding set_upt by simp
  then have "j \<in> set [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]" unfolding gupt_nc_186 .
  then show "gdc_sub None j" using gdc_nc_2976 gdc_nc_2977 gdc_nc_2978 gdc_nc_2979 gdc_nc_2980 gdc_nc_2981 gdc_nc_2982 gdc_nc_2983 gdc_nc_2984 gdc_nc_2985 gdc_nc_2986 gdc_nc_2987 gdc_nc_2988 gdc_nc_2989 gdc_nc_2990 gdc_nc_2991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
