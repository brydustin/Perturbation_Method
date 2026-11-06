theory GDCX_nc_129
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2064: "gdc_sub None 2064"
  by (gdc_eval gdc_nc_2064)

lemma gdc_nc_2065: "gdc_sub None 2065"
  by (gdc_eval gdc_nc_2065)

lemma gdc_nc_2066: "gdc_sub None 2066"
  by (gdc_eval gdc_nc_2066)

lemma gdc_nc_2067: "gdc_sub None 2067"
  by (gdc_eval gdc_nc_2067)

lemma gdc_nc_2068: "gdc_sub None 2068"
  by (gdc_eval gdc_nc_2068)

lemma gdc_nc_2069: "gdc_sub None 2069"
  by (gdc_eval gdc_nc_2069)

lemma gdc_nc_2070: "gdc_sub None 2070"
  by (gdc_eval gdc_nc_2070)

lemma gdc_nc_2071: "gdc_sub None 2071"
  by (gdc_eval gdc_nc_2071)

lemma gdc_nc_2072: "gdc_sub None 2072"
  by (gdc_eval gdc_nc_2072)

lemma gdc_nc_2073: "gdc_sub None 2073"
  by (gdc_eval gdc_nc_2073)

lemma gdc_nc_2074: "gdc_sub None 2074"
  by (gdc_eval gdc_nc_2074)

lemma gdc_nc_2075: "gdc_sub None 2075"
  by (gdc_eval gdc_nc_2075)

lemma gdc_nc_2076: "gdc_sub None 2076"
  by (gdc_eval gdc_nc_2076)

lemma gdc_nc_2077: "gdc_sub None 2077"
  by (gdc_eval gdc_nc_2077)

lemma gdc_nc_2078: "gdc_sub None 2078"
  by (gdc_eval gdc_nc_2078)

lemma gdc_nc_2079: "gdc_sub None 2079"
  by (gdc_eval gdc_nc_2079)

lemma gupt_nc_129: "[2064..<2080] = [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]"
  by (simp add: upt_rec)

lemma gsec_nc_129: "\<forall>j\<in>{16 * 129..<16 * 129 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 129..<16 * 129 + 16}"
  then have "j \<in> set [2064..<2080]" unfolding set_upt by simp
  then have "j \<in> set [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]" unfolding gupt_nc_129 .
  then show "gdc_sub None j" using gdc_nc_2064 gdc_nc_2065 gdc_nc_2066 gdc_nc_2067 gdc_nc_2068 gdc_nc_2069 gdc_nc_2070 gdc_nc_2071 gdc_nc_2072 gdc_nc_2073 gdc_nc_2074 gdc_nc_2075 gdc_nc_2076 gdc_nc_2077 gdc_nc_2078 gdc_nc_2079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
