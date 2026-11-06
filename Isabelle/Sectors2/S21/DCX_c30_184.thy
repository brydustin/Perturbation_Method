theory DCX_c30_184
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2944: "dc_sub dc_b30 2944"
  by (dc_eval dc_c30_2944)

lemma dc_c30_2945: "dc_sub dc_b30 2945"
  by (dc_eval dc_c30_2945)

lemma dc_c30_2946: "dc_sub dc_b30 2946"
  by (dc_eval dc_c30_2946)

lemma dc_c30_2947: "dc_sub dc_b30 2947"
  by (dc_eval dc_c30_2947)

lemma dc_c30_2948: "dc_sub dc_b30 2948"
  by (dc_eval dc_c30_2948)

lemma dc_c30_2949: "dc_sub dc_b30 2949"
  by (dc_eval dc_c30_2949)

lemma dc_c30_2950: "dc_sub dc_b30 2950"
  by (dc_eval dc_c30_2950)

lemma dc_c30_2951: "dc_sub dc_b30 2951"
  by (dc_eval dc_c30_2951)

lemma dc_c30_2952: "dc_sub dc_b30 2952"
  by (dc_eval dc_c30_2952)

lemma dc_c30_2953: "dc_sub dc_b30 2953"
  by (dc_eval dc_c30_2953)

lemma dc_c30_2954: "dc_sub dc_b30 2954"
  by (dc_eval dc_c30_2954)

lemma dc_c30_2955: "dc_sub dc_b30 2955"
  by (dc_eval dc_c30_2955)

lemma dc_c30_2956: "dc_sub dc_b30 2956"
  by (dc_eval dc_c30_2956)

lemma dc_c30_2957: "dc_sub dc_b30 2957"
  by (dc_eval dc_c30_2957)

lemma dc_c30_2958: "dc_sub dc_b30 2958"
  by (dc_eval dc_c30_2958)

lemma dc_c30_2959: "dc_sub dc_b30 2959"
  by (dc_eval dc_c30_2959)

lemma upt_c30_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma sec_c30_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding upt_c30_184 .
  then show "dc_sub dc_b30 j" using dc_c30_2944 dc_c30_2945 dc_c30_2946 dc_c30_2947 dc_c30_2948 dc_c30_2949 dc_c30_2950 dc_c30_2951 dc_c30_2952 dc_c30_2953 dc_c30_2954 dc_c30_2955 dc_c30_2956 dc_c30_2957 dc_c30_2958 dc_c30_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
