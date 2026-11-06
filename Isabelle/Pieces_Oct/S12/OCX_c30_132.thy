theory OCX_c30_132
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2112: "oc_sub oc_b30 2112"
  by (oc_eval oc_c30_2112)

lemma oc_c30_2113: "oc_sub oc_b30 2113"
  by (oc_eval oc_c30_2113)

lemma oc_c30_2114: "oc_sub oc_b30 2114"
  by (oc_eval oc_c30_2114)

lemma oc_c30_2115: "oc_sub oc_b30 2115"
  by (oc_eval oc_c30_2115)

lemma oc_c30_2116: "oc_sub oc_b30 2116"
  by (oc_eval oc_c30_2116)

lemma oc_c30_2117: "oc_sub oc_b30 2117"
  by (oc_eval oc_c30_2117)

lemma oc_c30_2118: "oc_sub oc_b30 2118"
  by (oc_eval oc_c30_2118)

lemma oc_c30_2119: "oc_sub oc_b30 2119"
  by (oc_eval oc_c30_2119)

lemma oc_c30_2120: "oc_sub oc_b30 2120"
  by (oc_eval oc_c30_2120)

lemma oc_c30_2121: "oc_sub oc_b30 2121"
  by (oc_eval oc_c30_2121)

lemma oc_c30_2122: "oc_sub oc_b30 2122"
  by (oc_eval oc_c30_2122)

lemma oc_c30_2123: "oc_sub oc_b30 2123"
  by (oc_eval oc_c30_2123)

lemma oc_c30_2124: "oc_sub oc_b30 2124"
  by (oc_eval oc_c30_2124)

lemma oc_c30_2125: "oc_sub oc_b30 2125"
  by (oc_eval oc_c30_2125)

lemma oc_c30_2126: "oc_sub oc_b30 2126"
  by (oc_eval oc_c30_2126)

lemma oc_c30_2127: "oc_sub oc_b30 2127"
  by (oc_eval oc_c30_2127)

lemma upt_c30_132: "[2112..<2128] = [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]"
  by (simp add: upt_rec)

lemma sec_c30_132: "\<forall>j\<in>{16 * 132..<16 * 132 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 132..<16 * 132 + 16}"
  then have "j \<in> set [2112..<2128]" unfolding set_upt by simp
  then have "j \<in> set [2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127]" unfolding upt_c30_132 .
  then show "oc_sub oc_b30 j" using oc_c30_2112 oc_c30_2113 oc_c30_2114 oc_c30_2115 oc_c30_2116 oc_c30_2117 oc_c30_2118 oc_c30_2119 oc_c30_2120 oc_c30_2121 oc_c30_2122 oc_c30_2123 oc_c30_2124 oc_c30_2125 oc_c30_2126 oc_c30_2127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
