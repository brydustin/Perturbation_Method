theory GOCX_nc_129
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2064: "goc_sub None 2064"
  by (goc_eval goc_nc_2064)

lemma goc_nc_2065: "goc_sub None 2065"
  by (goc_eval goc_nc_2065)

lemma goc_nc_2066: "goc_sub None 2066"
  by (goc_eval goc_nc_2066)

lemma goc_nc_2067: "goc_sub None 2067"
  by (goc_eval goc_nc_2067)

lemma goc_nc_2068: "goc_sub None 2068"
  by (goc_eval goc_nc_2068)

lemma goc_nc_2069: "goc_sub None 2069"
  by (goc_eval goc_nc_2069)

lemma goc_nc_2070: "goc_sub None 2070"
  by (goc_eval goc_nc_2070)

lemma goc_nc_2071: "goc_sub None 2071"
  by (goc_eval goc_nc_2071)

lemma goc_nc_2072: "goc_sub None 2072"
  by (goc_eval goc_nc_2072)

lemma goc_nc_2073: "goc_sub None 2073"
  by (goc_eval goc_nc_2073)

lemma goc_nc_2074: "goc_sub None 2074"
  by (goc_eval goc_nc_2074)

lemma goc_nc_2075: "goc_sub None 2075"
  by (goc_eval goc_nc_2075)

lemma goc_nc_2076: "goc_sub None 2076"
  by (goc_eval goc_nc_2076)

lemma goc_nc_2077: "goc_sub None 2077"
  by (goc_eval goc_nc_2077)

lemma goc_nc_2078: "goc_sub None 2078"
  by (goc_eval goc_nc_2078)

lemma goc_nc_2079: "goc_sub None 2079"
  by (goc_eval goc_nc_2079)

lemma gupt_nc_129: "[2064..<2080] = [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]"
  by (simp add: upt_rec)

lemma gsec_nc_129: "\<forall>j\<in>{16 * 129..<16 * 129 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 129..<16 * 129 + 16}"
  then have "j \<in> set [2064..<2080]" unfolding set_upt by simp
  then have "j \<in> set [2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079]" unfolding gupt_nc_129 .
  then show "goc_sub None j" using goc_nc_2064 goc_nc_2065 goc_nc_2066 goc_nc_2067 goc_nc_2068 goc_nc_2069 goc_nc_2070 goc_nc_2071 goc_nc_2072 goc_nc_2073 goc_nc_2074 goc_nc_2075 goc_nc_2076 goc_nc_2077 goc_nc_2078 goc_nc_2079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
