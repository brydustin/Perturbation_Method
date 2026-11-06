theory DCX_c30_134
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2144: "dc_sub dc_b30 2144"
  by (dc_eval dc_c30_2144)

lemma dc_c30_2145: "dc_sub dc_b30 2145"
  by (dc_eval dc_c30_2145)

lemma dc_c30_2146: "dc_sub dc_b30 2146"
  by (dc_eval dc_c30_2146)

lemma dc_c30_2147: "dc_sub dc_b30 2147"
  by (dc_eval dc_c30_2147)

lemma dc_c30_2148: "dc_sub dc_b30 2148"
  by (dc_eval dc_c30_2148)

lemma dc_c30_2149: "dc_sub dc_b30 2149"
  by (dc_eval dc_c30_2149)

lemma dc_c30_2150: "dc_sub dc_b30 2150"
  by (dc_eval dc_c30_2150)

lemma dc_c30_2151: "dc_sub dc_b30 2151"
  by (dc_eval dc_c30_2151)

lemma dc_c30_2152: "dc_sub dc_b30 2152"
  by (dc_eval dc_c30_2152)

lemma dc_c30_2153: "dc_sub dc_b30 2153"
  by (dc_eval dc_c30_2153)

lemma dc_c30_2154: "dc_sub dc_b30 2154"
  by (dc_eval dc_c30_2154)

lemma dc_c30_2155: "dc_sub dc_b30 2155"
  by (dc_eval dc_c30_2155)

lemma dc_c30_2156: "dc_sub dc_b30 2156"
  by (dc_eval dc_c30_2156)

lemma dc_c30_2157: "dc_sub dc_b30 2157"
  by (dc_eval dc_c30_2157)

lemma dc_c30_2158: "dc_sub dc_b30 2158"
  by (dc_eval dc_c30_2158)

lemma dc_c30_2159: "dc_sub dc_b30 2159"
  by (dc_eval dc_c30_2159)

lemma upt_c30_134: "[2144..<2160] = [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]"
  by (simp add: upt_rec)

lemma sec_c30_134: "\<forall>j\<in>{16 * 134..<16 * 134 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 134..<16 * 134 + 16}"
  then have "j \<in> set [2144..<2160]" unfolding set_upt by simp
  then have "j \<in> set [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]" unfolding upt_c30_134 .
  then show "dc_sub dc_b30 j" using dc_c30_2144 dc_c30_2145 dc_c30_2146 dc_c30_2147 dc_c30_2148 dc_c30_2149 dc_c30_2150 dc_c30_2151 dc_c30_2152 dc_c30_2153 dc_c30_2154 dc_c30_2155 dc_c30_2156 dc_c30_2157 dc_c30_2158 dc_c30_2159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
