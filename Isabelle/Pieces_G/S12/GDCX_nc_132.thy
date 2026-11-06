theory GDCX_nc_132
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2112: "gdc_sub None 2112"
  by (gdc_eval gdc_nc_2112)

lemma gdc_nc_2113: "gdc_sub None 2113"
  by (gdc_eval gdc_nc_2113)

lemma gdc_nc_2114: "gdc_sub None 2114"
  by (gdc_eval gdc_nc_2114)

lemma gdc_nc_2115: "gdc_sub None 2115"
  by (gdc_eval gdc_nc_2115)

lemma gdc_nc_2116: "gdc_sub None 2116"
  by (gdc_eval gdc_nc_2116)

lemma gdc_nc_2117: "gdc_sub None 2117"
  by (gdc_eval gdc_nc_2117)

lemma gdc_nc_2118: "gdc_sub None 2118"
  by (gdc_eval gdc_nc_2118)

lemma gdc_nc_2119: "gdc_sub None 2119"
  by (gdc_eval gdc_nc_2119)

lemma gdc_nc_2120: "gdc_sub None 2120"
  by (gdc_eval gdc_nc_2120)

lemma gdc_nc_2121: "gdc_sub None 2121"
  by (gdc_eval gdc_nc_2121)

lemma gdc_nc_2122: "gdc_sub None 2122"
  by (gdc_eval gdc_nc_2122)

lemma gdc_nc_2123: "gdc_sub None 2123"
  by (gdc_eval gdc_nc_2123)

lemma gdc_nc_2124: "gdc_sub None 2124"
  by (gdc_eval gdc_nc_2124)

lemma gdc_nc_2125: "gdc_sub None 2125"
  by (gdc_eval gdc_nc_2125)

lemma gdc_nc_2126: "gdc_sub None 2126"
  by (gdc_eval gdc_nc_2126)

lemma gdc_nc_2127: "gdc_sub None 2127"
  by (gdc_eval gdc_nc_2127)

lemma gupt_nc_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma gsec_nc_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding gupt_nc_132 .
  then show "gdc_sub None j" using gdc_nc_2112 gdc_nc_2113 gdc_nc_2114 gdc_nc_2115 gdc_nc_2116 gdc_nc_2117 gdc_nc_2118 gdc_nc_2119 gdc_nc_2120 gdc_nc_2121 gdc_nc_2122 gdc_nc_2123 gdc_nc_2124 gdc_nc_2125 gdc_nc_2126 gdc_nc_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
