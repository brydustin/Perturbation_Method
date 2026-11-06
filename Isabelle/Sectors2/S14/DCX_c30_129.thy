theory DCX_c30_129
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2064: "dc_sub dc_b30 2064"
  by (dc_eval dc_c30_2064)

lemma dc_c30_2065: "dc_sub dc_b30 2065"
  by (dc_eval dc_c30_2065)

lemma dc_c30_2066: "dc_sub dc_b30 2066"
  by (dc_eval dc_c30_2066)

lemma dc_c30_2067: "dc_sub dc_b30 2067"
  by (dc_eval dc_c30_2067)

lemma dc_c30_2068: "dc_sub dc_b30 2068"
  by (dc_eval dc_c30_2068)

lemma dc_c30_2069: "dc_sub dc_b30 2069"
  by (dc_eval dc_c30_2069)

lemma dc_c30_2070: "dc_sub dc_b30 2070"
  by (dc_eval dc_c30_2070)

lemma dc_c30_2071: "dc_sub dc_b30 2071"
  by (dc_eval dc_c30_2071)

lemma dc_c30_2072: "dc_sub dc_b30 2072"
  by (dc_eval dc_c30_2072)

lemma dc_c30_2073: "dc_sub dc_b30 2073"
  by (dc_eval dc_c30_2073)

lemma dc_c30_2074: "dc_sub dc_b30 2074"
  by (dc_eval dc_c30_2074)

lemma dc_c30_2075: "dc_sub dc_b30 2075"
  by (dc_eval dc_c30_2075)

lemma dc_c30_2076: "dc_sub dc_b30 2076"
  by (dc_eval dc_c30_2076)

lemma dc_c30_2077: "dc_sub dc_b30 2077"
  by (dc_eval dc_c30_2077)

lemma dc_c30_2078: "dc_sub dc_b30 2078"
  by (dc_eval dc_c30_2078)

lemma dc_c30_2079: "dc_sub dc_b30 2079"
  by (dc_eval dc_c30_2079)

lemma upt_c30_129: "[2064..<2080] = [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]"
  by (simp add: upt_rec)

lemma sec_c30_129: "\<forall>j\<in>{16 * 129..<16 * 129 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 129..<16 * 129 + 16}"
  then have "j \<in> set [2064..<2080]" unfolding set_upt by simp
  then have "j \<in> set [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]" unfolding upt_c30_129 .
  then show "dc_sub dc_b30 j" using dc_c30_2064 dc_c30_2065 dc_c30_2066 dc_c30_2067 dc_c30_2068 dc_c30_2069 dc_c30_2070 dc_c30_2071 dc_c30_2072 dc_c30_2073 dc_c30_2074 dc_c30_2075 dc_c30_2076 dc_c30_2077 dc_c30_2078 dc_c30_2079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
