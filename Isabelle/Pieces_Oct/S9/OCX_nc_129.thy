theory OCX_nc_129
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2064: "oc_sub None 2064"
  by (oc_eval oc_nc_2064)

lemma oc_nc_2065: "oc_sub None 2065"
  by (oc_eval oc_nc_2065)

lemma oc_nc_2066: "oc_sub None 2066"
  by (oc_eval oc_nc_2066)

lemma oc_nc_2067: "oc_sub None 2067"
  by (oc_eval oc_nc_2067)

lemma oc_nc_2068: "oc_sub None 2068"
  by (oc_eval oc_nc_2068)

lemma oc_nc_2069: "oc_sub None 2069"
  by (oc_eval oc_nc_2069)

lemma oc_nc_2070: "oc_sub None 2070"
  by (oc_eval oc_nc_2070)

lemma oc_nc_2071: "oc_sub None 2071"
  by (oc_eval oc_nc_2071)

lemma oc_nc_2072: "oc_sub None 2072"
  by (oc_eval oc_nc_2072)

lemma oc_nc_2073: "oc_sub None 2073"
  by (oc_eval oc_nc_2073)

lemma oc_nc_2074: "oc_sub None 2074"
  by (oc_eval oc_nc_2074)

lemma oc_nc_2075: "oc_sub None 2075"
  by (oc_eval oc_nc_2075)

lemma oc_nc_2076: "oc_sub None 2076"
  by (oc_eval oc_nc_2076)

lemma oc_nc_2077: "oc_sub None 2077"
  by (oc_eval oc_nc_2077)

lemma oc_nc_2078: "oc_sub None 2078"
  by (oc_eval oc_nc_2078)

lemma oc_nc_2079: "oc_sub None 2079"
  by (oc_eval oc_nc_2079)

lemma upt_nc_129: "[2064..<2080] = [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]"
  by (simp add: upt_rec)

lemma sec_nc_129: "\<forall>j\<in>{16 * 129..<16 * 129 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 129..<16 * 129 + 16}"
  then have "j \<in> set [2064..<2080]" unfolding set_upt by simp
  then have "j \<in> set [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]" unfolding upt_nc_129 .
  then show "oc_sub None j" using oc_nc_2064 oc_nc_2065 oc_nc_2066 oc_nc_2067 oc_nc_2068 oc_nc_2069 oc_nc_2070 oc_nc_2071 oc_nc_2072 oc_nc_2073 oc_nc_2074 oc_nc_2075 oc_nc_2076 oc_nc_2077 oc_nc_2078 oc_nc_2079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
