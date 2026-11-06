theory OCX_c30_131
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2096: "oc_sub oc_b30 2096"
  by (oc_eval oc_c30_2096)

lemma oc_c30_2097: "oc_sub oc_b30 2097"
  by (oc_eval oc_c30_2097)

lemma oc_c30_2098: "oc_sub oc_b30 2098"
  by (oc_eval oc_c30_2098)

lemma oc_c30_2099: "oc_sub oc_b30 2099"
  by (oc_eval oc_c30_2099)

lemma oc_c30_2100: "oc_sub oc_b30 2100"
  by (oc_eval oc_c30_2100)

lemma oc_c30_2101: "oc_sub oc_b30 2101"
  by (oc_eval oc_c30_2101)

lemma oc_c30_2102: "oc_sub oc_b30 2102"
  by (oc_eval oc_c30_2102)

lemma oc_c30_2103: "oc_sub oc_b30 2103"
  by (oc_eval oc_c30_2103)

lemma oc_c30_2104: "oc_sub oc_b30 2104"
  by (oc_eval oc_c30_2104)

lemma oc_c30_2105: "oc_sub oc_b30 2105"
  by (oc_eval oc_c30_2105)

lemma oc_c30_2106: "oc_sub oc_b30 2106"
  by (oc_eval oc_c30_2106)

lemma oc_c30_2107: "oc_sub oc_b30 2107"
  by (oc_eval oc_c30_2107)

lemma oc_c30_2108: "oc_sub oc_b30 2108"
  by (oc_eval oc_c30_2108)

lemma oc_c30_2109: "oc_sub oc_b30 2109"
  by (oc_eval oc_c30_2109)

lemma oc_c30_2110: "oc_sub oc_b30 2110"
  by (oc_eval oc_c30_2110)

lemma oc_c30_2111: "oc_sub oc_b30 2111"
  by (oc_eval oc_c30_2111)

lemma upt_c30_131: "[2096..<2112] = [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]"
  by (simp add: upt_rec)

lemma sec_c30_131: "\<forall>j\<in>{16 * 131..<16 * 131 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 131..<16 * 131 + 16}"
  then have "j \<in> set [2096..<2112]" unfolding set_upt by simp
  then have "j \<in> set [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]" unfolding upt_c30_131 .
  then show "oc_sub oc_b30 j" using oc_c30_2096 oc_c30_2097 oc_c30_2098 oc_c30_2099 oc_c30_2100 oc_c30_2101 oc_c30_2102 oc_c30_2103 oc_c30_2104 oc_c30_2105 oc_c30_2106 oc_c30_2107 oc_c30_2108 oc_c30_2109 oc_c30_2110 oc_c30_2111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
