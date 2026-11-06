theory GOCX_nc_061
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0976: "goc_sub None 976"
  by (goc_eval goc_nc_0976)

lemma goc_nc_0977: "goc_sub None 977"
  by (goc_eval goc_nc_0977)

lemma goc_nc_0978: "goc_sub None 978"
  by (goc_eval goc_nc_0978)

lemma goc_nc_0979: "goc_sub None 979"
  by (goc_eval goc_nc_0979)

lemma goc_nc_0980: "goc_sub None 980"
  by (goc_eval goc_nc_0980)

lemma goc_nc_0981: "goc_sub None 981"
  by (goc_eval goc_nc_0981)

lemma goc_nc_0982: "goc_sub None 982"
  by (goc_eval goc_nc_0982)

lemma goc_nc_0983: "goc_sub None 983"
  by (goc_eval goc_nc_0983)

lemma goc_nc_0984: "goc_sub None 984"
  by (goc_eval goc_nc_0984)

lemma goc_nc_0985: "goc_sub None 985"
  by (goc_eval goc_nc_0985)

lemma goc_nc_0986: "goc_sub None 986"
  by (goc_eval goc_nc_0986)

lemma goc_nc_0987: "goc_sub None 987"
  by (goc_eval goc_nc_0987)

lemma goc_nc_0988: "goc_sub None 988"
  by (goc_eval goc_nc_0988)

lemma goc_nc_0989: "goc_sub None 989"
  by (goc_eval goc_nc_0989)

lemma goc_nc_0990: "goc_sub None 990"
  by (goc_eval goc_nc_0990)

lemma goc_nc_0991: "goc_sub None 991"
  by (goc_eval goc_nc_0991)

lemma gupt_nc_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma gsec_nc_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding gupt_nc_061 .
  then show "goc_sub None j" using goc_nc_0976 goc_nc_0977 goc_nc_0978 goc_nc_0979 goc_nc_0980 goc_nc_0981 goc_nc_0982 goc_nc_0983 goc_nc_0984 goc_nc_0985 goc_nc_0986 goc_nc_0987 goc_nc_0988 goc_nc_0989 goc_nc_0990 goc_nc_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
