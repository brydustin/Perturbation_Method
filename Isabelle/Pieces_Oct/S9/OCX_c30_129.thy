theory OCX_c30_129
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2064: "oc_sub oc_b30 2064"
  by (oc_eval oc_c30_2064)

lemma oc_c30_2065: "oc_sub oc_b30 2065"
  by (oc_eval oc_c30_2065)

lemma oc_c30_2066: "oc_sub oc_b30 2066"
  by (oc_eval oc_c30_2066)

lemma oc_c30_2067: "oc_sub oc_b30 2067"
  by (oc_eval oc_c30_2067)

lemma oc_c30_2068: "oc_sub oc_b30 2068"
  by (oc_eval oc_c30_2068)

lemma oc_c30_2069: "oc_sub oc_b30 2069"
  by (oc_eval oc_c30_2069)

lemma oc_c30_2070: "oc_sub oc_b30 2070"
  by (oc_eval oc_c30_2070)

lemma oc_c30_2071: "oc_sub oc_b30 2071"
  by (oc_eval oc_c30_2071)

lemma oc_c30_2072: "oc_sub oc_b30 2072"
  by (oc_eval oc_c30_2072)

lemma oc_c30_2073: "oc_sub oc_b30 2073"
  by (oc_eval oc_c30_2073)

lemma oc_c30_2074: "oc_sub oc_b30 2074"
  by (oc_eval oc_c30_2074)

lemma oc_c30_2075: "oc_sub oc_b30 2075"
  by (oc_eval oc_c30_2075)

lemma oc_c30_2076: "oc_sub oc_b30 2076"
  by (oc_eval oc_c30_2076)

lemma oc_c30_2077: "oc_sub oc_b30 2077"
  by (oc_eval oc_c30_2077)

lemma oc_c30_2078: "oc_sub oc_b30 2078"
  by (oc_eval oc_c30_2078)

lemma oc_c30_2079: "oc_sub oc_b30 2079"
  by (oc_eval oc_c30_2079)

lemma upt_c30_129: "[2064..<2080] = [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]"
  by (simp add: upt_rec)

lemma sec_c30_129: "\<forall>j\<in>{16 * 129..<16 * 129 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 129..<16 * 129 + 16}"
  then have "j \<in> set [2064..<2080]" unfolding set_upt by simp
  then have "j \<in> set [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]" unfolding upt_c30_129 .
  then show "oc_sub oc_b30 j" using oc_c30_2064 oc_c30_2065 oc_c30_2066 oc_c30_2067 oc_c30_2068 oc_c30_2069 oc_c30_2070 oc_c30_2071 oc_c30_2072 oc_c30_2073 oc_c30_2074 oc_c30_2075 oc_c30_2076 oc_c30_2077 oc_c30_2078 oc_c30_2079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
