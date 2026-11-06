theory GDCX_nc_059
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0944: "gdc_sub None 944"
  by (gdc_eval gdc_nc_0944)

lemma gdc_nc_0945: "gdc_sub None 945"
  by (gdc_eval gdc_nc_0945)

lemma gdc_nc_0946: "gdc_sub None 946"
  by (gdc_eval gdc_nc_0946)

lemma gdc_nc_0947: "gdc_sub None 947"
  by (gdc_eval gdc_nc_0947)

lemma gdc_nc_0948: "gdc_sub None 948"
  by (gdc_eval gdc_nc_0948)

lemma gdc_nc_0949: "gdc_sub None 949"
  by (gdc_eval gdc_nc_0949)

lemma gdc_nc_0950: "gdc_sub None 950"
  by (gdc_eval gdc_nc_0950)

lemma gdc_nc_0951: "gdc_sub None 951"
  by (gdc_eval gdc_nc_0951)

lemma gdc_nc_0952: "gdc_sub None 952"
  by (gdc_eval gdc_nc_0952)

lemma gdc_nc_0953: "gdc_sub None 953"
  by (gdc_eval gdc_nc_0953)

lemma gdc_nc_0954: "gdc_sub None 954"
  by (gdc_eval gdc_nc_0954)

lemma gdc_nc_0955: "gdc_sub None 955"
  by (gdc_eval gdc_nc_0955)

lemma gdc_nc_0956: "gdc_sub None 956"
  by (gdc_eval gdc_nc_0956)

lemma gdc_nc_0957: "gdc_sub None 957"
  by (gdc_eval gdc_nc_0957)

lemma gdc_nc_0958: "gdc_sub None 958"
  by (gdc_eval gdc_nc_0958)

lemma gdc_nc_0959: "gdc_sub None 959"
  by (gdc_eval gdc_nc_0959)

lemma gupt_nc_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma gsec_nc_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding gupt_nc_059 .
  then show "gdc_sub None j" using gdc_nc_0944 gdc_nc_0945 gdc_nc_0946 gdc_nc_0947 gdc_nc_0948 gdc_nc_0949 gdc_nc_0950 gdc_nc_0951 gdc_nc_0952 gdc_nc_0953 gdc_nc_0954 gdc_nc_0955 gdc_nc_0956 gdc_nc_0957 gdc_nc_0958 gdc_nc_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
