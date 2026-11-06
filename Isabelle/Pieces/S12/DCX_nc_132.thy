theory DCX_nc_132
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2112: "dc_sub None 2112"
  by (dc_eval dc_nc_2112)

lemma dc_nc_2113: "dc_sub None 2113"
  by (dc_eval dc_nc_2113)

lemma dc_nc_2114: "dc_sub None 2114"
  by (dc_eval dc_nc_2114)

lemma dc_nc_2115: "dc_sub None 2115"
  by (dc_eval dc_nc_2115)

lemma dc_nc_2116: "dc_sub None 2116"
  by (dc_eval dc_nc_2116)

lemma dc_nc_2117: "dc_sub None 2117"
  by (dc_eval dc_nc_2117)

lemma dc_nc_2118: "dc_sub None 2118"
  by (dc_eval dc_nc_2118)

lemma dc_nc_2119: "dc_sub None 2119"
  by (dc_eval dc_nc_2119)

lemma dc_nc_2120: "dc_sub None 2120"
  by (dc_eval dc_nc_2120)

lemma dc_nc_2121: "dc_sub None 2121"
  by (dc_eval dc_nc_2121)

lemma dc_nc_2122: "dc_sub None 2122"
  by (dc_eval dc_nc_2122)

lemma dc_nc_2123: "dc_sub None 2123"
  by (dc_eval dc_nc_2123)

lemma dc_nc_2124: "dc_sub None 2124"
  by (dc_eval dc_nc_2124)

lemma dc_nc_2125: "dc_sub None 2125"
  by (dc_eval dc_nc_2125)

lemma dc_nc_2126: "dc_sub None 2126"
  by (dc_eval dc_nc_2126)

lemma dc_nc_2127: "dc_sub None 2127"
  by (dc_eval dc_nc_2127)

lemma upt_nc_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma sec_nc_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding upt_nc_132 .
  then show "dc_sub None j" using dc_nc_2112 dc_nc_2113 dc_nc_2114 dc_nc_2115 dc_nc_2116 dc_nc_2117 dc_nc_2118 dc_nc_2119 dc_nc_2120 dc_nc_2121 dc_nc_2122 dc_nc_2123 dc_nc_2124 dc_nc_2125 dc_nc_2126 dc_nc_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
