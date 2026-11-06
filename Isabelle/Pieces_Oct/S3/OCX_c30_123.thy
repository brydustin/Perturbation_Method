theory OCX_c30_123
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1968: "oc_sub oc_b30 1968"
  by (oc_eval oc_c30_1968)

lemma oc_c30_1969: "oc_sub oc_b30 1969"
  by (oc_eval oc_c30_1969)

lemma oc_c30_1970: "oc_sub oc_b30 1970"
  by (oc_eval oc_c30_1970)

lemma oc_c30_1971: "oc_sub oc_b30 1971"
  by (oc_eval oc_c30_1971)

lemma oc_c30_1972: "oc_sub oc_b30 1972"
  by (oc_eval oc_c30_1972)

lemma oc_c30_1973: "oc_sub oc_b30 1973"
  by (oc_eval oc_c30_1973)

lemma oc_c30_1974: "oc_sub oc_b30 1974"
  by (oc_eval oc_c30_1974)

lemma oc_c30_1975: "oc_sub oc_b30 1975"
  by (oc_eval oc_c30_1975)

lemma oc_c30_1976: "oc_sub oc_b30 1976"
  by (oc_eval oc_c30_1976)

lemma oc_c30_1977: "oc_sub oc_b30 1977"
  by (oc_eval oc_c30_1977)

lemma oc_c30_1978: "oc_sub oc_b30 1978"
  by (oc_eval oc_c30_1978)

lemma oc_c30_1979: "oc_sub oc_b30 1979"
  by (oc_eval oc_c30_1979)

lemma oc_c30_1980: "oc_sub oc_b30 1980"
  by (oc_eval oc_c30_1980)

lemma oc_c30_1981: "oc_sub oc_b30 1981"
  by (oc_eval oc_c30_1981)

lemma oc_c30_1982: "oc_sub oc_b30 1982"
  by (oc_eval oc_c30_1982)

lemma oc_c30_1983: "oc_sub oc_b30 1983"
  by (oc_eval oc_c30_1983)

lemma upt_c30_123: "[1968..<1984] = [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]"
  by (simp add: upt_rec)

lemma sec_c30_123: "\<forall>j\<in>{16 * 123..<16 * 123 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 123..<16 * 123 + 16}"
  then have "j \<in> set [1968..<1984]" unfolding set_upt by simp
  then have "j \<in> set [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]" unfolding upt_c30_123 .
  then show "oc_sub oc_b30 j" using oc_c30_1968 oc_c30_1969 oc_c30_1970 oc_c30_1971 oc_c30_1972 oc_c30_1973 oc_c30_1974 oc_c30_1975 oc_c30_1976 oc_c30_1977 oc_c30_1978 oc_c30_1979 oc_c30_1980 oc_c30_1981 oc_c30_1982 oc_c30_1983
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
