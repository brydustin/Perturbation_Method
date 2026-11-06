theory DCX_c30_132
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2112: "dc_sub dc_b30 2112"
  by (dc_eval dc_c30_2112)

lemma dc_c30_2113: "dc_sub dc_b30 2113"
  by (dc_eval dc_c30_2113)

lemma dc_c30_2114: "dc_sub dc_b30 2114"
  by (dc_eval dc_c30_2114)

lemma dc_c30_2115: "dc_sub dc_b30 2115"
  by (dc_eval dc_c30_2115)

lemma dc_c30_2116: "dc_sub dc_b30 2116"
  by (dc_eval dc_c30_2116)

lemma dc_c30_2117: "dc_sub dc_b30 2117"
  by (dc_eval dc_c30_2117)

lemma dc_c30_2118: "dc_sub dc_b30 2118"
  by (dc_eval dc_c30_2118)

lemma dc_c30_2119: "dc_sub dc_b30 2119"
  by (dc_eval dc_c30_2119)

lemma dc_c30_2120: "dc_sub dc_b30 2120"
  by (dc_eval dc_c30_2120)

lemma dc_c30_2121: "dc_sub dc_b30 2121"
  by (dc_eval dc_c30_2121)

lemma dc_c30_2122: "dc_sub dc_b30 2122"
  by (dc_eval dc_c30_2122)

lemma dc_c30_2123: "dc_sub dc_b30 2123"
  by (dc_eval dc_c30_2123)

lemma dc_c30_2124: "dc_sub dc_b30 2124"
  by (dc_eval dc_c30_2124)

lemma dc_c30_2125: "dc_sub dc_b30 2125"
  by (dc_eval dc_c30_2125)

lemma dc_c30_2126: "dc_sub dc_b30 2126"
  by (dc_eval dc_c30_2126)

lemma dc_c30_2127: "dc_sub dc_b30 2127"
  by (dc_eval dc_c30_2127)

lemma upt_c30_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma sec_c30_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding upt_c30_132 .
  then show "dc_sub dc_b30 j" using dc_c30_2112 dc_c30_2113 dc_c30_2114 dc_c30_2115 dc_c30_2116 dc_c30_2117 dc_c30_2118 dc_c30_2119 dc_c30_2120 dc_c30_2121 dc_c30_2122 dc_c30_2123 dc_c30_2124 dc_c30_2125 dc_c30_2126 dc_c30_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
