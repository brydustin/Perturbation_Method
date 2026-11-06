theory DCX_nc_138
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2208: "dc_sub None 2208"
  by (dc_eval dc_nc_2208)

lemma dc_nc_2209: "dc_sub None 2209"
  by (dc_eval dc_nc_2209)

lemma dc_nc_2210: "dc_sub None 2210"
  by (dc_eval dc_nc_2210)

lemma dc_nc_2211: "dc_sub None 2211"
  by (dc_eval dc_nc_2211)

lemma dc_nc_2212: "dc_sub None 2212"
  by (dc_eval dc_nc_2212)

lemma dc_nc_2213: "dc_sub None 2213"
  by (dc_eval dc_nc_2213)

lemma dc_nc_2214: "dc_sub None 2214"
  by (dc_eval dc_nc_2214)

lemma dc_nc_2215: "dc_sub None 2215"
  by (dc_eval dc_nc_2215)

lemma dc_nc_2216: "dc_sub None 2216"
  by (dc_eval dc_nc_2216)

lemma dc_nc_2217: "dc_sub None 2217"
  by (dc_eval dc_nc_2217)

lemma dc_nc_2218: "dc_sub None 2218"
  by (dc_eval dc_nc_2218)

lemma dc_nc_2219: "dc_sub None 2219"
  by (dc_eval dc_nc_2219)

lemma dc_nc_2220: "dc_sub None 2220"
  by (dc_eval dc_nc_2220)

lemma dc_nc_2221: "dc_sub None 2221"
  by (dc_eval dc_nc_2221)

lemma dc_nc_2222: "dc_sub None 2222"
  by (dc_eval dc_nc_2222)

lemma dc_nc_2223: "dc_sub None 2223"
  by (dc_eval dc_nc_2223)

lemma upt_nc_138: "[2208..<2224] = [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]"
  by (simp add: upt_rec)

lemma sec_nc_138: "\<forall>j\<in>{16 * 138..<16 * 138 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 138..<16 * 138 + 16}"
  then have "j \<in> set [2208..<2224]" unfolding set_upt by simp
  then have "j \<in> set [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]" unfolding upt_nc_138 .
  then show "dc_sub None j" using dc_nc_2208 dc_nc_2209 dc_nc_2210 dc_nc_2211 dc_nc_2212 dc_nc_2213 dc_nc_2214 dc_nc_2215 dc_nc_2216 dc_nc_2217 dc_nc_2218 dc_nc_2219 dc_nc_2220 dc_nc_2221 dc_nc_2222 dc_nc_2223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
