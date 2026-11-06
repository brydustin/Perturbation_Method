theory DCX_c30_061
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0976: "dc_sub dc_b30 976"
  by (dc_eval dc_c30_0976)

lemma dc_c30_0977: "dc_sub dc_b30 977"
  by (dc_eval dc_c30_0977)

lemma dc_c30_0978: "dc_sub dc_b30 978"
  by (dc_eval dc_c30_0978)

lemma dc_c30_0979: "dc_sub dc_b30 979"
  by (dc_eval dc_c30_0979)

lemma dc_c30_0980: "dc_sub dc_b30 980"
  by (dc_eval dc_c30_0980)

lemma dc_c30_0981: "dc_sub dc_b30 981"
  by (dc_eval dc_c30_0981)

lemma dc_c30_0982: "dc_sub dc_b30 982"
  by (dc_eval dc_c30_0982)

lemma dc_c30_0983: "dc_sub dc_b30 983"
  by (dc_eval dc_c30_0983)

lemma dc_c30_0984: "dc_sub dc_b30 984"
  by (dc_eval dc_c30_0984)

lemma dc_c30_0985: "dc_sub dc_b30 985"
  by (dc_eval dc_c30_0985)

lemma dc_c30_0986: "dc_sub dc_b30 986"
  by (dc_eval dc_c30_0986)

lemma dc_c30_0987: "dc_sub dc_b30 987"
  by (dc_eval dc_c30_0987)

lemma dc_c30_0988: "dc_sub dc_b30 988"
  by (dc_eval dc_c30_0988)

lemma dc_c30_0989: "dc_sub dc_b30 989"
  by (dc_eval dc_c30_0989)

lemma dc_c30_0990: "dc_sub dc_b30 990"
  by (dc_eval dc_c30_0990)

lemma dc_c30_0991: "dc_sub dc_b30 991"
  by (dc_eval dc_c30_0991)

lemma upt_c30_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma sec_c30_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding upt_c30_061 .
  then show "dc_sub dc_b30 j" using dc_c30_0976 dc_c30_0977 dc_c30_0978 dc_c30_0979 dc_c30_0980 dc_c30_0981 dc_c30_0982 dc_c30_0983 dc_c30_0984 dc_c30_0985 dc_c30_0986 dc_c30_0987 dc_c30_0988 dc_c30_0989 dc_c30_0990 dc_c30_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
