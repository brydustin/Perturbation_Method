theory GOCX_nc_138
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2208: "goc_sub None 2208"
  by (goc_eval goc_nc_2208)

lemma goc_nc_2209: "goc_sub None 2209"
  by (goc_eval goc_nc_2209)

lemma goc_nc_2210: "goc_sub None 2210"
  by (goc_eval goc_nc_2210)

lemma goc_nc_2211: "goc_sub None 2211"
  by (goc_eval goc_nc_2211)

lemma goc_nc_2212: "goc_sub None 2212"
  by (goc_eval goc_nc_2212)

lemma goc_nc_2213: "goc_sub None 2213"
  by (goc_eval goc_nc_2213)

lemma goc_nc_2214: "goc_sub None 2214"
  by (goc_eval goc_nc_2214)

lemma goc_nc_2215: "goc_sub None 2215"
  by (goc_eval goc_nc_2215)

lemma goc_nc_2216: "goc_sub None 2216"
  by (goc_eval goc_nc_2216)

lemma goc_nc_2217: "goc_sub None 2217"
  by (goc_eval goc_nc_2217)

lemma goc_nc_2218: "goc_sub None 2218"
  by (goc_eval goc_nc_2218)

lemma goc_nc_2219: "goc_sub None 2219"
  by (goc_eval goc_nc_2219)

lemma goc_nc_2220: "goc_sub None 2220"
  by (goc_eval goc_nc_2220)

lemma goc_nc_2221: "goc_sub None 2221"
  by (goc_eval goc_nc_2221)

lemma goc_nc_2222: "goc_sub None 2222"
  by (goc_eval goc_nc_2222)

lemma goc_nc_2223: "goc_sub None 2223"
  by (goc_eval goc_nc_2223)

lemma gupt_nc_138: "[2208..<2224] = [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]"
  by (simp add: upt_rec)

lemma gsec_nc_138: "\<forall>j\<in>{16 * 138..<16 * 138 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 138..<16 * 138 + 16}"
  then have "j \<in> set [2208..<2224]" unfolding set_upt by simp
  then have "j \<in> set [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]" unfolding gupt_nc_138 .
  then show "goc_sub None j" using goc_nc_2208 goc_nc_2209 goc_nc_2210 goc_nc_2211 goc_nc_2212 goc_nc_2213 goc_nc_2214 goc_nc_2215 goc_nc_2216 goc_nc_2217 goc_nc_2218 goc_nc_2219 goc_nc_2220 goc_nc_2221 goc_nc_2222 goc_nc_2223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
