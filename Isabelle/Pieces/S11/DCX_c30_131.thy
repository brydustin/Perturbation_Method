theory DCX_c30_131
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2096: "dc_sub dc_b30 2096"
  by (dc_eval dc_c30_2096)

lemma dc_c30_2097: "dc_sub dc_b30 2097"
  by (dc_eval dc_c30_2097)

lemma dc_c30_2098: "dc_sub dc_b30 2098"
  by (dc_eval dc_c30_2098)

lemma dc_c30_2099: "dc_sub dc_b30 2099"
  by (dc_eval dc_c30_2099)

lemma dc_c30_2100: "dc_sub dc_b30 2100"
  by (dc_eval dc_c30_2100)

lemma dc_c30_2101: "dc_sub dc_b30 2101"
  by (dc_eval dc_c30_2101)

lemma dc_c30_2102: "dc_sub dc_b30 2102"
  by (dc_eval dc_c30_2102)

lemma dc_c30_2103: "dc_sub dc_b30 2103"
  by (dc_eval dc_c30_2103)

lemma dc_c30_2104: "dc_sub dc_b30 2104"
  by (dc_eval dc_c30_2104)

lemma dc_c30_2105: "dc_sub dc_b30 2105"
  by (dc_eval dc_c30_2105)

lemma dc_c30_2106: "dc_sub dc_b30 2106"
  by (dc_eval dc_c30_2106)

lemma dc_c30_2107: "dc_sub dc_b30 2107"
  by (dc_eval dc_c30_2107)

lemma dc_c30_2108: "dc_sub dc_b30 2108"
  by (dc_eval dc_c30_2108)

lemma dc_c30_2109: "dc_sub dc_b30 2109"
  by (dc_eval dc_c30_2109)

lemma dc_c30_2110: "dc_sub dc_b30 2110"
  by (dc_eval dc_c30_2110)

lemma dc_c30_2111: "dc_sub dc_b30 2111"
  by (dc_eval dc_c30_2111)

lemma upt_c30_131: "[2096..<2112] = [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]"
  by (simp add: upt_rec)

lemma sec_c30_131: "\<forall>j\<in>{16 * 131..<16 * 131 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 131..<16 * 131 + 16}"
  then have "j \<in> set [2096..<2112]" unfolding set_upt by simp
  then have "j \<in> set [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]" unfolding upt_c30_131 .
  then show "dc_sub dc_b30 j" using dc_c30_2096 dc_c30_2097 dc_c30_2098 dc_c30_2099 dc_c30_2100 dc_c30_2101 dc_c30_2102 dc_c30_2103 dc_c30_2104 dc_c30_2105 dc_c30_2106 dc_c30_2107 dc_c30_2108 dc_c30_2109 dc_c30_2110 dc_c30_2111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
