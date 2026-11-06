theory GOCX_nc_134
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2144: "goc_sub None 2144"
  by (goc_eval goc_nc_2144)

lemma goc_nc_2145: "goc_sub None 2145"
  by (goc_eval goc_nc_2145)

lemma goc_nc_2146: "goc_sub None 2146"
  by (goc_eval goc_nc_2146)

lemma goc_nc_2147: "goc_sub None 2147"
  by (goc_eval goc_nc_2147)

lemma goc_nc_2148: "goc_sub None 2148"
  by (goc_eval goc_nc_2148)

lemma goc_nc_2149: "goc_sub None 2149"
  by (goc_eval goc_nc_2149)

lemma goc_nc_2150: "goc_sub None 2150"
  by (goc_eval goc_nc_2150)

lemma goc_nc_2151: "goc_sub None 2151"
  by (goc_eval goc_nc_2151)

lemma goc_nc_2152: "goc_sub None 2152"
  by (goc_eval goc_nc_2152)

lemma goc_nc_2153: "goc_sub None 2153"
  by (goc_eval goc_nc_2153)

lemma goc_nc_2154: "goc_sub None 2154"
  by (goc_eval goc_nc_2154)

lemma goc_nc_2155: "goc_sub None 2155"
  by (goc_eval goc_nc_2155)

lemma goc_nc_2156: "goc_sub None 2156"
  by (goc_eval goc_nc_2156)

lemma goc_nc_2157: "goc_sub None 2157"
  by (goc_eval goc_nc_2157)

lemma goc_nc_2158: "goc_sub None 2158"
  by (goc_eval goc_nc_2158)

lemma goc_nc_2159: "goc_sub None 2159"
  by (goc_eval goc_nc_2159)

lemma gupt_nc_134: "[2144..<2160] = [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]"
  by (simp add: upt_rec)

lemma gsec_nc_134: "\<forall>j\<in>{16 * 134..<16 * 134 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 134..<16 * 134 + 16}"
  then have "j \<in> set [2144..<2160]" unfolding set_upt by simp
  then have "j \<in> set [2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159]" unfolding gupt_nc_134 .
  then show "goc_sub None j" using goc_nc_2144 goc_nc_2145 goc_nc_2146 goc_nc_2147 goc_nc_2148 goc_nc_2149 goc_nc_2150 goc_nc_2151 goc_nc_2152 goc_nc_2153 goc_nc_2154 goc_nc_2155 goc_nc_2156 goc_nc_2157 goc_nc_2158 goc_nc_2159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
