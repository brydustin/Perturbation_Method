theory DCX_nc_184
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2944: "dc_sub None 2944"
  by (dc_eval dc_nc_2944)

lemma dc_nc_2945: "dc_sub None 2945"
  by (dc_eval dc_nc_2945)

lemma dc_nc_2946: "dc_sub None 2946"
  by (dc_eval dc_nc_2946)

lemma dc_nc_2947: "dc_sub None 2947"
  by (dc_eval dc_nc_2947)

lemma dc_nc_2948: "dc_sub None 2948"
  by (dc_eval dc_nc_2948)

lemma dc_nc_2949: "dc_sub None 2949"
  by (dc_eval dc_nc_2949)

lemma dc_nc_2950: "dc_sub None 2950"
  by (dc_eval dc_nc_2950)

lemma dc_nc_2951: "dc_sub None 2951"
  by (dc_eval dc_nc_2951)

lemma dc_nc_2952: "dc_sub None 2952"
  by (dc_eval dc_nc_2952)

lemma dc_nc_2953: "dc_sub None 2953"
  by (dc_eval dc_nc_2953)

lemma dc_nc_2954: "dc_sub None 2954"
  by (dc_eval dc_nc_2954)

lemma dc_nc_2955: "dc_sub None 2955"
  by (dc_eval dc_nc_2955)

lemma dc_nc_2956: "dc_sub None 2956"
  by (dc_eval dc_nc_2956)

lemma dc_nc_2957: "dc_sub None 2957"
  by (dc_eval dc_nc_2957)

lemma dc_nc_2958: "dc_sub None 2958"
  by (dc_eval dc_nc_2958)

lemma dc_nc_2959: "dc_sub None 2959"
  by (dc_eval dc_nc_2959)

lemma upt_nc_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma sec_nc_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding upt_nc_184 .
  then show "dc_sub None j" using dc_nc_2944 dc_nc_2945 dc_nc_2946 dc_nc_2947 dc_nc_2948 dc_nc_2949 dc_nc_2950 dc_nc_2951 dc_nc_2952 dc_nc_2953 dc_nc_2954 dc_nc_2955 dc_nc_2956 dc_nc_2957 dc_nc_2958 dc_nc_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
