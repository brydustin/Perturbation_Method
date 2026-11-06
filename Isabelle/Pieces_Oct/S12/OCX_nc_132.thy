theory OCX_nc_132
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2112: "oc_sub None 2112"
  by (oc_eval oc_nc_2112)

lemma oc_nc_2113: "oc_sub None 2113"
  by (oc_eval oc_nc_2113)

lemma oc_nc_2114: "oc_sub None 2114"
  by (oc_eval oc_nc_2114)

lemma oc_nc_2115: "oc_sub None 2115"
  by (oc_eval oc_nc_2115)

lemma oc_nc_2116: "oc_sub None 2116"
  by (oc_eval oc_nc_2116)

lemma oc_nc_2117: "oc_sub None 2117"
  by (oc_eval oc_nc_2117)

lemma oc_nc_2118: "oc_sub None 2118"
  by (oc_eval oc_nc_2118)

lemma oc_nc_2119: "oc_sub None 2119"
  by (oc_eval oc_nc_2119)

lemma oc_nc_2120: "oc_sub None 2120"
  by (oc_eval oc_nc_2120)

lemma oc_nc_2121: "oc_sub None 2121"
  by (oc_eval oc_nc_2121)

lemma oc_nc_2122: "oc_sub None 2122"
  by (oc_eval oc_nc_2122)

lemma oc_nc_2123: "oc_sub None 2123"
  by (oc_eval oc_nc_2123)

lemma oc_nc_2124: "oc_sub None 2124"
  by (oc_eval oc_nc_2124)

lemma oc_nc_2125: "oc_sub None 2125"
  by (oc_eval oc_nc_2125)

lemma oc_nc_2126: "oc_sub None 2126"
  by (oc_eval oc_nc_2126)

lemma oc_nc_2127: "oc_sub None 2127"
  by (oc_eval oc_nc_2127)

lemma upt_nc_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma sec_nc_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding upt_nc_132 .
  then show "oc_sub None j" using oc_nc_2112 oc_nc_2113 oc_nc_2114 oc_nc_2115 oc_nc_2116 oc_nc_2117 oc_nc_2118 oc_nc_2119 oc_nc_2120 oc_nc_2121 oc_nc_2122 oc_nc_2123 oc_nc_2124 oc_nc_2125 oc_nc_2126 oc_nc_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
