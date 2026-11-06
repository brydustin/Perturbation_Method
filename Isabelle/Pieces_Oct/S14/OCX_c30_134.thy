theory OCX_c30_134
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2144: "oc_sub oc_b30 2144"
  by (oc_eval oc_c30_2144)

lemma oc_c30_2145: "oc_sub oc_b30 2145"
  by (oc_eval oc_c30_2145)

lemma oc_c30_2146: "oc_sub oc_b30 2146"
  by (oc_eval oc_c30_2146)

lemma oc_c30_2147: "oc_sub oc_b30 2147"
  by (oc_eval oc_c30_2147)

lemma oc_c30_2148: "oc_sub oc_b30 2148"
  by (oc_eval oc_c30_2148)

lemma oc_c30_2149: "oc_sub oc_b30 2149"
  by (oc_eval oc_c30_2149)

lemma oc_c30_2150: "oc_sub oc_b30 2150"
  by (oc_eval oc_c30_2150)

lemma oc_c30_2151: "oc_sub oc_b30 2151"
  by (oc_eval oc_c30_2151)

lemma oc_c30_2152: "oc_sub oc_b30 2152"
  by (oc_eval oc_c30_2152)

lemma oc_c30_2153: "oc_sub oc_b30 2153"
  by (oc_eval oc_c30_2153)

lemma oc_c30_2154: "oc_sub oc_b30 2154"
  by (oc_eval oc_c30_2154)

lemma oc_c30_2155: "oc_sub oc_b30 2155"
  by (oc_eval oc_c30_2155)

lemma oc_c30_2156: "oc_sub oc_b30 2156"
  by (oc_eval oc_c30_2156)

lemma oc_c30_2157: "oc_sub oc_b30 2157"
  by (oc_eval oc_c30_2157)

lemma oc_c30_2158: "oc_sub oc_b30 2158"
  by (oc_eval oc_c30_2158)

lemma oc_c30_2159: "oc_sub oc_b30 2159"
  by (oc_eval oc_c30_2159)

lemma upt_c30_134: "[2144..<2160] = [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]"
  by (simp add: upt_rec)

lemma sec_c30_134: "\<forall>j\<in>{16 * 134..<16 * 134 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 134..<16 * 134 + 16}"
  then have "j \<in> set [2144..<2160]" unfolding set_upt by simp
  then have "j \<in> set [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]" unfolding upt_c30_134 .
  then show "oc_sub oc_b30 j" using oc_c30_2144 oc_c30_2145 oc_c30_2146 oc_c30_2147 oc_c30_2148 oc_c30_2149 oc_c30_2150 oc_c30_2151 oc_c30_2152 oc_c30_2153 oc_c30_2154 oc_c30_2155 oc_c30_2156 oc_c30_2157 oc_c30_2158 oc_c30_2159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
