theory DCX_c30_123
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1968: "dc_sub dc_b30 1968"
  by (dc_eval dc_c30_1968)

lemma dc_c30_1969: "dc_sub dc_b30 1969"
  by (dc_eval dc_c30_1969)

lemma dc_c30_1970: "dc_sub dc_b30 1970"
  by (dc_eval dc_c30_1970)

lemma dc_c30_1971: "dc_sub dc_b30 1971"
  by (dc_eval dc_c30_1971)

lemma dc_c30_1972: "dc_sub dc_b30 1972"
  by (dc_eval dc_c30_1972)

lemma dc_c30_1973: "dc_sub dc_b30 1973"
  by (dc_eval dc_c30_1973)

lemma dc_c30_1974: "dc_sub dc_b30 1974"
  by (dc_eval dc_c30_1974)

lemma dc_c30_1975: "dc_sub dc_b30 1975"
  by (dc_eval dc_c30_1975)

lemma dc_c30_1976: "dc_sub dc_b30 1976"
  by (dc_eval dc_c30_1976)

lemma dc_c30_1977: "dc_sub dc_b30 1977"
  by (dc_eval dc_c30_1977)

lemma dc_c30_1978: "dc_sub dc_b30 1978"
  by (dc_eval dc_c30_1978)

lemma dc_c30_1979: "dc_sub dc_b30 1979"
  by (dc_eval dc_c30_1979)

lemma dc_c30_1980: "dc_sub dc_b30 1980"
  by (dc_eval dc_c30_1980)

lemma dc_c30_1981: "dc_sub dc_b30 1981"
  by (dc_eval dc_c30_1981)

lemma dc_c30_1982: "dc_sub dc_b30 1982"
  by (dc_eval dc_c30_1982)

lemma dc_c30_1983: "dc_sub dc_b30 1983"
  by (dc_eval dc_c30_1983)

lemma upt_c30_123: "[1968..<1984] = [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]"
  by (simp add: upt_rec)

lemma sec_c30_123: "\<forall>j\<in>{16 * 123..<16 * 123 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 123..<16 * 123 + 16}"
  then have "j \<in> set [1968..<1984]" unfolding set_upt by simp
  then have "j \<in> set [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]" unfolding upt_c30_123 .
  then show "dc_sub dc_b30 j" using dc_c30_1968 dc_c30_1969 dc_c30_1970 dc_c30_1971 dc_c30_1972 dc_c30_1973 dc_c30_1974 dc_c30_1975 dc_c30_1976 dc_c30_1977 dc_c30_1978 dc_c30_1979 dc_c30_1980 dc_c30_1981 dc_c30_1982 dc_c30_1983
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
