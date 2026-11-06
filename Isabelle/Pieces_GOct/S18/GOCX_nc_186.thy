theory GOCX_nc_186
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2976: "goc_sub None 2976"
  by (goc_eval goc_nc_2976)

lemma goc_nc_2977: "goc_sub None 2977"
  by (goc_eval goc_nc_2977)

lemma goc_nc_2978: "goc_sub None 2978"
  by (goc_eval goc_nc_2978)

lemma goc_nc_2979: "goc_sub None 2979"
  by (goc_eval goc_nc_2979)

lemma goc_nc_2980: "goc_sub None 2980"
  by (goc_eval goc_nc_2980)

lemma goc_nc_2981: "goc_sub None 2981"
  by (goc_eval goc_nc_2981)

lemma goc_nc_2982: "goc_sub None 2982"
  by (goc_eval goc_nc_2982)

lemma goc_nc_2983: "goc_sub None 2983"
  by (goc_eval goc_nc_2983)

lemma goc_nc_2984: "goc_sub None 2984"
  by (goc_eval goc_nc_2984)

lemma goc_nc_2985: "goc_sub None 2985"
  by (goc_eval goc_nc_2985)

lemma goc_nc_2986: "goc_sub None 2986"
  by (goc_eval goc_nc_2986)

lemma goc_nc_2987: "goc_sub None 2987"
  by (goc_eval goc_nc_2987)

lemma goc_nc_2988: "goc_sub None 2988"
  by (goc_eval goc_nc_2988)

lemma goc_nc_2989: "goc_sub None 2989"
  by (goc_eval goc_nc_2989)

lemma goc_nc_2990: "goc_sub None 2990"
  by (goc_eval goc_nc_2990)

lemma goc_nc_2991: "goc_sub None 2991"
  by (goc_eval goc_nc_2991)

lemma gupt_nc_186: "[2976..<2992] = [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]"
  by (simp add: upt_rec)

lemma gsec_nc_186: "\<forall>j\<in>{16 * 186..<16 * 186 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 186..<16 * 186 + 16}"
  then have "j \<in> set [2976..<2992]" unfolding set_upt by simp
  then have "j \<in> set [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]" unfolding gupt_nc_186 .
  then show "goc_sub None j" using goc_nc_2976 goc_nc_2977 goc_nc_2978 goc_nc_2979 goc_nc_2980 goc_nc_2981 goc_nc_2982 goc_nc_2983 goc_nc_2984 goc_nc_2985 goc_nc_2986 goc_nc_2987 goc_nc_2988 goc_nc_2989 goc_nc_2990 goc_nc_2991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
