theory DCX_nc_061
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0976: "dc_sub None 976"
  by (dc_eval dc_nc_0976)

lemma dc_nc_0977: "dc_sub None 977"
  by (dc_eval dc_nc_0977)

lemma dc_nc_0978: "dc_sub None 978"
  by (dc_eval dc_nc_0978)

lemma dc_nc_0979: "dc_sub None 979"
  by (dc_eval dc_nc_0979)

lemma dc_nc_0980: "dc_sub None 980"
  by (dc_eval dc_nc_0980)

lemma dc_nc_0981: "dc_sub None 981"
  by (dc_eval dc_nc_0981)

lemma dc_nc_0982: "dc_sub None 982"
  by (dc_eval dc_nc_0982)

lemma dc_nc_0983: "dc_sub None 983"
  by (dc_eval dc_nc_0983)

lemma dc_nc_0984: "dc_sub None 984"
  by (dc_eval dc_nc_0984)

lemma dc_nc_0985: "dc_sub None 985"
  by (dc_eval dc_nc_0985)

lemma dc_nc_0986: "dc_sub None 986"
  by (dc_eval dc_nc_0986)

lemma dc_nc_0987: "dc_sub None 987"
  by (dc_eval dc_nc_0987)

lemma dc_nc_0988: "dc_sub None 988"
  by (dc_eval dc_nc_0988)

lemma dc_nc_0989: "dc_sub None 989"
  by (dc_eval dc_nc_0989)

lemma dc_nc_0990: "dc_sub None 990"
  by (dc_eval dc_nc_0990)

lemma dc_nc_0991: "dc_sub None 991"
  by (dc_eval dc_nc_0991)

lemma upt_nc_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma sec_nc_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding upt_nc_061 .
  then show "dc_sub None j" using dc_nc_0976 dc_nc_0977 dc_nc_0978 dc_nc_0979 dc_nc_0980 dc_nc_0981 dc_nc_0982 dc_nc_0983 dc_nc_0984 dc_nc_0985 dc_nc_0986 dc_nc_0987 dc_nc_0988 dc_nc_0989 dc_nc_0990 dc_nc_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
