theory GOCX_nc_131
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2096: "goc_sub None 2096"
  by (goc_eval goc_nc_2096)

lemma goc_nc_2097: "goc_sub None 2097"
  by (goc_eval goc_nc_2097)

lemma goc_nc_2098: "goc_sub None 2098"
  by (goc_eval goc_nc_2098)

lemma goc_nc_2099: "goc_sub None 2099"
  by (goc_eval goc_nc_2099)

lemma goc_nc_2100: "goc_sub None 2100"
  by (goc_eval goc_nc_2100)

lemma goc_nc_2101: "goc_sub None 2101"
  by (goc_eval goc_nc_2101)

lemma goc_nc_2102: "goc_sub None 2102"
  by (goc_eval goc_nc_2102)

lemma goc_nc_2103: "goc_sub None 2103"
  by (goc_eval goc_nc_2103)

lemma goc_nc_2104: "goc_sub None 2104"
  by (goc_eval goc_nc_2104)

lemma goc_nc_2105: "goc_sub None 2105"
  by (goc_eval goc_nc_2105)

lemma goc_nc_2106: "goc_sub None 2106"
  by (goc_eval goc_nc_2106)

lemma goc_nc_2107: "goc_sub None 2107"
  by (goc_eval goc_nc_2107)

lemma goc_nc_2108: "goc_sub None 2108"
  by (goc_eval goc_nc_2108)

lemma goc_nc_2109: "goc_sub None 2109"
  by (goc_eval goc_nc_2109)

lemma goc_nc_2110: "goc_sub None 2110"
  by (goc_eval goc_nc_2110)

lemma goc_nc_2111: "goc_sub None 2111"
  by (goc_eval goc_nc_2111)

lemma gupt_nc_131: "[2096..<2112] = [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]"
  by (simp add: upt_rec)

lemma gsec_nc_131: "\<forall>j\<in>{16 * 131..<16 * 131 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 131..<16 * 131 + 16}"
  then have "j \<in> set [2096..<2112]" unfolding set_upt by simp
  then have "j \<in> set [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111]" unfolding gupt_nc_131 .
  then show "goc_sub None j" using goc_nc_2096 goc_nc_2097 goc_nc_2098 goc_nc_2099 goc_nc_2100 goc_nc_2101 goc_nc_2102 goc_nc_2103 goc_nc_2104 goc_nc_2105 goc_nc_2106 goc_nc_2107 goc_nc_2108 goc_nc_2109 goc_nc_2110 goc_nc_2111
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
