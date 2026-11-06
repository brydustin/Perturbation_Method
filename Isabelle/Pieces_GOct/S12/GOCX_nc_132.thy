theory GOCX_nc_132
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2112: "goc_sub None 2112"
  by (goc_eval goc_nc_2112)

lemma goc_nc_2113: "goc_sub None 2113"
  by (goc_eval goc_nc_2113)

lemma goc_nc_2114: "goc_sub None 2114"
  by (goc_eval goc_nc_2114)

lemma goc_nc_2115: "goc_sub None 2115"
  by (goc_eval goc_nc_2115)

lemma goc_nc_2116: "goc_sub None 2116"
  by (goc_eval goc_nc_2116)

lemma goc_nc_2117: "goc_sub None 2117"
  by (goc_eval goc_nc_2117)

lemma goc_nc_2118: "goc_sub None 2118"
  by (goc_eval goc_nc_2118)

lemma goc_nc_2119: "goc_sub None 2119"
  by (goc_eval goc_nc_2119)

lemma goc_nc_2120: "goc_sub None 2120"
  by (goc_eval goc_nc_2120)

lemma goc_nc_2121: "goc_sub None 2121"
  by (goc_eval goc_nc_2121)

lemma goc_nc_2122: "goc_sub None 2122"
  by (goc_eval goc_nc_2122)

lemma goc_nc_2123: "goc_sub None 2123"
  by (goc_eval goc_nc_2123)

lemma goc_nc_2124: "goc_sub None 2124"
  by (goc_eval goc_nc_2124)

lemma goc_nc_2125: "goc_sub None 2125"
  by (goc_eval goc_nc_2125)

lemma goc_nc_2126: "goc_sub None 2126"
  by (goc_eval goc_nc_2126)

lemma goc_nc_2127: "goc_sub None 2127"
  by (goc_eval goc_nc_2127)

lemma gupt_nc_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma gsec_nc_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding gupt_nc_132 .
  then show "goc_sub None j" using goc_nc_2112 goc_nc_2113 goc_nc_2114 goc_nc_2115 goc_nc_2116 goc_nc_2117 goc_nc_2118 goc_nc_2119 goc_nc_2120 goc_nc_2121 goc_nc_2122 goc_nc_2123 goc_nc_2124 goc_nc_2125 goc_nc_2126 goc_nc_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
