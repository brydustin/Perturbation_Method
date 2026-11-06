theory GDCX_nc_061
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0976: "gdc_sub None 976"
  by (gdc_eval gdc_nc_0976)

lemma gdc_nc_0977: "gdc_sub None 977"
  by (gdc_eval gdc_nc_0977)

lemma gdc_nc_0978: "gdc_sub None 978"
  by (gdc_eval gdc_nc_0978)

lemma gdc_nc_0979: "gdc_sub None 979"
  by (gdc_eval gdc_nc_0979)

lemma gdc_nc_0980: "gdc_sub None 980"
  by (gdc_eval gdc_nc_0980)

lemma gdc_nc_0981: "gdc_sub None 981"
  by (gdc_eval gdc_nc_0981)

lemma gdc_nc_0982: "gdc_sub None 982"
  by (gdc_eval gdc_nc_0982)

lemma gdc_nc_0983: "gdc_sub None 983"
  by (gdc_eval gdc_nc_0983)

lemma gdc_nc_0984: "gdc_sub None 984"
  by (gdc_eval gdc_nc_0984)

lemma gdc_nc_0985: "gdc_sub None 985"
  by (gdc_eval gdc_nc_0985)

lemma gdc_nc_0986: "gdc_sub None 986"
  by (gdc_eval gdc_nc_0986)

lemma gdc_nc_0987: "gdc_sub None 987"
  by (gdc_eval gdc_nc_0987)

lemma gdc_nc_0988: "gdc_sub None 988"
  by (gdc_eval gdc_nc_0988)

lemma gdc_nc_0989: "gdc_sub None 989"
  by (gdc_eval gdc_nc_0989)

lemma gdc_nc_0990: "gdc_sub None 990"
  by (gdc_eval gdc_nc_0990)

lemma gdc_nc_0991: "gdc_sub None 991"
  by (gdc_eval gdc_nc_0991)

lemma gupt_nc_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma gsec_nc_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding gupt_nc_061 .
  then show "gdc_sub None j" using gdc_nc_0976 gdc_nc_0977 gdc_nc_0978 gdc_nc_0979 gdc_nc_0980 gdc_nc_0981 gdc_nc_0982 gdc_nc_0983 gdc_nc_0984 gdc_nc_0985 gdc_nc_0986 gdc_nc_0987 gdc_nc_0988 gdc_nc_0989 gdc_nc_0990 gdc_nc_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
