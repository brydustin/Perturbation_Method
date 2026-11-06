theory GDCX_nc_184
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2944: "gdc_sub None 2944"
  by (gdc_eval gdc_nc_2944)

lemma gdc_nc_2945: "gdc_sub None 2945"
  by (gdc_eval gdc_nc_2945)

lemma gdc_nc_2946: "gdc_sub None 2946"
  by (gdc_eval gdc_nc_2946)

lemma gdc_nc_2947: "gdc_sub None 2947"
  by (gdc_eval gdc_nc_2947)

lemma gdc_nc_2948: "gdc_sub None 2948"
  by (gdc_eval gdc_nc_2948)

lemma gdc_nc_2949: "gdc_sub None 2949"
  by (gdc_eval gdc_nc_2949)

lemma gdc_nc_2950: "gdc_sub None 2950"
  by (gdc_eval gdc_nc_2950)

lemma gdc_nc_2951: "gdc_sub None 2951"
  by (gdc_eval gdc_nc_2951)

lemma gdc_nc_2952: "gdc_sub None 2952"
  by (gdc_eval gdc_nc_2952)

lemma gdc_nc_2953: "gdc_sub None 2953"
  by (gdc_eval gdc_nc_2953)

lemma gdc_nc_2954: "gdc_sub None 2954"
  by (gdc_eval gdc_nc_2954)

lemma gdc_nc_2955: "gdc_sub None 2955"
  by (gdc_eval gdc_nc_2955)

lemma gdc_nc_2956: "gdc_sub None 2956"
  by (gdc_eval gdc_nc_2956)

lemma gdc_nc_2957: "gdc_sub None 2957"
  by (gdc_eval gdc_nc_2957)

lemma gdc_nc_2958: "gdc_sub None 2958"
  by (gdc_eval gdc_nc_2958)

lemma gdc_nc_2959: "gdc_sub None 2959"
  by (gdc_eval gdc_nc_2959)

lemma gupt_nc_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma gsec_nc_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding gupt_nc_184 .
  then show "gdc_sub None j" using gdc_nc_2944 gdc_nc_2945 gdc_nc_2946 gdc_nc_2947 gdc_nc_2948 gdc_nc_2949 gdc_nc_2950 gdc_nc_2951 gdc_nc_2952 gdc_nc_2953 gdc_nc_2954 gdc_nc_2955 gdc_nc_2956 gdc_nc_2957 gdc_nc_2958 gdc_nc_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
