theory OCX_nc_131
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2096: "oc_sub None 2096"
  by (oc_eval oc_nc_2096)

lemma oc_nc_2097: "oc_sub None 2097"
  by (oc_eval oc_nc_2097)

lemma oc_nc_2098: "oc_sub None 2098"
  by (oc_eval oc_nc_2098)

lemma oc_nc_2099: "oc_sub None 2099"
  by (oc_eval oc_nc_2099)

lemma oc_nc_2100: "oc_sub None 2100"
  by (oc_eval oc_nc_2100)

lemma oc_nc_2101: "oc_sub None 2101"
  by (oc_eval oc_nc_2101)

lemma oc_nc_2102: "oc_sub None 2102"
  by (oc_eval oc_nc_2102)

lemma oc_nc_2103: "oc_sub None 2103"
  by (oc_eval oc_nc_2103)

lemma oc_nc_2104: "oc_sub None 2104"
  by (oc_eval oc_nc_2104)

lemma oc_nc_2105: "oc_sub None 2105"
  by (oc_eval oc_nc_2105)

lemma oc_nc_2106: "oc_sub None 2106"
  by (oc_eval oc_nc_2106)

lemma oc_nc_2107: "oc_sub None 2107"
  by (oc_eval oc_nc_2107)

lemma oc_nc_2108: "oc_sub None 2108"
  by (oc_eval oc_nc_2108)

lemma oc_nc_2109: "oc_sub None 2109"
  by (oc_eval oc_nc_2109)

lemma oc_nc_2110: "oc_sub None 2110"
  by (oc_eval oc_nc_2110)

lemma oc_nc_2111: "oc_sub None 2111"
  by (oc_eval oc_nc_2111)

lemma upt_nc_131: "[2096..<2112] = [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]"
  by (simp add: upt_rec)

lemma sec_nc_131: "\<forall>j\<in>{16 * 131..<16 * 131 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 131..<16 * 131 + 16}"
  then have "j \<in> set [2096..<2112]" unfolding set_upt by simp
  then have "j \<in> set [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]" unfolding upt_nc_131 .
  then show "oc_sub None j" using oc_nc_2096 oc_nc_2097 oc_nc_2098 oc_nc_2099 oc_nc_2100 oc_nc_2101 oc_nc_2102 oc_nc_2103 oc_nc_2104 oc_nc_2105 oc_nc_2106 oc_nc_2107 oc_nc_2108 oc_nc_2109 oc_nc_2110 oc_nc_2111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
