theory OCX_nc_061
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0976: "oc_sub None 976"
  by (oc_eval oc_nc_0976)

lemma oc_nc_0977: "oc_sub None 977"
  by (oc_eval oc_nc_0977)

lemma oc_nc_0978: "oc_sub None 978"
  by (oc_eval oc_nc_0978)

lemma oc_nc_0979: "oc_sub None 979"
  by (oc_eval oc_nc_0979)

lemma oc_nc_0980: "oc_sub None 980"
  by (oc_eval oc_nc_0980)

lemma oc_nc_0981: "oc_sub None 981"
  by (oc_eval oc_nc_0981)

lemma oc_nc_0982: "oc_sub None 982"
  by (oc_eval oc_nc_0982)

lemma oc_nc_0983: "oc_sub None 983"
  by (oc_eval oc_nc_0983)

lemma oc_nc_0984: "oc_sub None 984"
  by (oc_eval oc_nc_0984)

lemma oc_nc_0985: "oc_sub None 985"
  by (oc_eval oc_nc_0985)

lemma oc_nc_0986: "oc_sub None 986"
  by (oc_eval oc_nc_0986)

lemma oc_nc_0987: "oc_sub None 987"
  by (oc_eval oc_nc_0987)

lemma oc_nc_0988: "oc_sub None 988"
  by (oc_eval oc_nc_0988)

lemma oc_nc_0989: "oc_sub None 989"
  by (oc_eval oc_nc_0989)

lemma oc_nc_0990: "oc_sub None 990"
  by (oc_eval oc_nc_0990)

lemma oc_nc_0991: "oc_sub None 991"
  by (oc_eval oc_nc_0991)

lemma upt_nc_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma sec_nc_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding upt_nc_061 .
  then show "oc_sub None j" using oc_nc_0976 oc_nc_0977 oc_nc_0978 oc_nc_0979 oc_nc_0980 oc_nc_0981 oc_nc_0982 oc_nc_0983 oc_nc_0984 oc_nc_0985 oc_nc_0986 oc_nc_0987 oc_nc_0988 oc_nc_0989 oc_nc_0990 oc_nc_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
