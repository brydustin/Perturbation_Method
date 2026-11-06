theory OCX_nc_134
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2144: "oc_sub None 2144"
  by (oc_eval oc_nc_2144)

lemma oc_nc_2145: "oc_sub None 2145"
  by (oc_eval oc_nc_2145)

lemma oc_nc_2146: "oc_sub None 2146"
  by (oc_eval oc_nc_2146)

lemma oc_nc_2147: "oc_sub None 2147"
  by (oc_eval oc_nc_2147)

lemma oc_nc_2148: "oc_sub None 2148"
  by (oc_eval oc_nc_2148)

lemma oc_nc_2149: "oc_sub None 2149"
  by (oc_eval oc_nc_2149)

lemma oc_nc_2150: "oc_sub None 2150"
  by (oc_eval oc_nc_2150)

lemma oc_nc_2151: "oc_sub None 2151"
  by (oc_eval oc_nc_2151)

lemma oc_nc_2152: "oc_sub None 2152"
  by (oc_eval oc_nc_2152)

lemma oc_nc_2153: "oc_sub None 2153"
  by (oc_eval oc_nc_2153)

lemma oc_nc_2154: "oc_sub None 2154"
  by (oc_eval oc_nc_2154)

lemma oc_nc_2155: "oc_sub None 2155"
  by (oc_eval oc_nc_2155)

lemma oc_nc_2156: "oc_sub None 2156"
  by (oc_eval oc_nc_2156)

lemma oc_nc_2157: "oc_sub None 2157"
  by (oc_eval oc_nc_2157)

lemma oc_nc_2158: "oc_sub None 2158"
  by (oc_eval oc_nc_2158)

lemma oc_nc_2159: "oc_sub None 2159"
  by (oc_eval oc_nc_2159)

lemma upt_nc_134: "[2144..<2160] = [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]"
  by (simp add: upt_rec)

lemma sec_nc_134: "\<forall>j\<in>{16 * 134..<16 * 134 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 134..<16 * 134 + 16}"
  then have "j \<in> set [2144..<2160]" unfolding set_upt by simp
  then have "j \<in> set [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]" unfolding upt_nc_134 .
  then show "oc_sub None j" using oc_nc_2144 oc_nc_2145 oc_nc_2146 oc_nc_2147 oc_nc_2148 oc_nc_2149 oc_nc_2150 oc_nc_2151 oc_nc_2152 oc_nc_2153 oc_nc_2154 oc_nc_2155 oc_nc_2156 oc_nc_2157 oc_nc_2158 oc_nc_2159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
