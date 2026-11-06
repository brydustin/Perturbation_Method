theory OCX_c30_061
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0976: "oc_sub oc_b30 976"
  by (oc_eval oc_c30_0976)

lemma oc_c30_0977: "oc_sub oc_b30 977"
  by (oc_eval oc_c30_0977)

lemma oc_c30_0978: "oc_sub oc_b30 978"
  by (oc_eval oc_c30_0978)

lemma oc_c30_0979: "oc_sub oc_b30 979"
  by (oc_eval oc_c30_0979)

lemma oc_c30_0980: "oc_sub oc_b30 980"
  by (oc_eval oc_c30_0980)

lemma oc_c30_0981: "oc_sub oc_b30 981"
  by (oc_eval oc_c30_0981)

lemma oc_c30_0982: "oc_sub oc_b30 982"
  by (oc_eval oc_c30_0982)

lemma oc_c30_0983: "oc_sub oc_b30 983"
  by (oc_eval oc_c30_0983)

lemma oc_c30_0984: "oc_sub oc_b30 984"
  by (oc_eval oc_c30_0984)

lemma oc_c30_0985: "oc_sub oc_b30 985"
  by (oc_eval oc_c30_0985)

lemma oc_c30_0986: "oc_sub oc_b30 986"
  by (oc_eval oc_c30_0986)

lemma oc_c30_0987: "oc_sub oc_b30 987"
  by (oc_eval oc_c30_0987)

lemma oc_c30_0988: "oc_sub oc_b30 988"
  by (oc_eval oc_c30_0988)

lemma oc_c30_0989: "oc_sub oc_b30 989"
  by (oc_eval oc_c30_0989)

lemma oc_c30_0990: "oc_sub oc_b30 990"
  by (oc_eval oc_c30_0990)

lemma oc_c30_0991: "oc_sub oc_b30 991"
  by (oc_eval oc_c30_0991)

lemma upt_c30_061: "[976..<992] = [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]"
  by (simp add: upt_rec)

lemma sec_c30_061: "\<forall>j\<in>{16 * 61..<16 * 61 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 61..<16 * 61 + 16}"
  then have "j \<in> set [976..<992]" unfolding set_upt by simp
  then have "j \<in> set [976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]" unfolding upt_c30_061 .
  then show "oc_sub oc_b30 j" using oc_c30_0976 oc_c30_0977 oc_c30_0978 oc_c30_0979 oc_c30_0980 oc_c30_0981 oc_c30_0982 oc_c30_0983 oc_c30_0984 oc_c30_0985 oc_c30_0986 oc_c30_0987 oc_c30_0988 oc_c30_0989 oc_c30_0990 oc_c30_0991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
