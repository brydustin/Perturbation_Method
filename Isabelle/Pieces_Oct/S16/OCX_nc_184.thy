theory OCX_nc_184
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2944: "oc_sub None 2944"
  by (oc_eval oc_nc_2944)

lemma oc_nc_2945: "oc_sub None 2945"
  by (oc_eval oc_nc_2945)

lemma oc_nc_2946: "oc_sub None 2946"
  by (oc_eval oc_nc_2946)

lemma oc_nc_2947: "oc_sub None 2947"
  by (oc_eval oc_nc_2947)

lemma oc_nc_2948: "oc_sub None 2948"
  by (oc_eval oc_nc_2948)

lemma oc_nc_2949: "oc_sub None 2949"
  by (oc_eval oc_nc_2949)

lemma oc_nc_2950: "oc_sub None 2950"
  by (oc_eval oc_nc_2950)

lemma oc_nc_2951: "oc_sub None 2951"
  by (oc_eval oc_nc_2951)

lemma oc_nc_2952: "oc_sub None 2952"
  by (oc_eval oc_nc_2952)

lemma oc_nc_2953: "oc_sub None 2953"
  by (oc_eval oc_nc_2953)

lemma oc_nc_2954: "oc_sub None 2954"
  by (oc_eval oc_nc_2954)

lemma oc_nc_2955: "oc_sub None 2955"
  by (oc_eval oc_nc_2955)

lemma oc_nc_2956: "oc_sub None 2956"
  by (oc_eval oc_nc_2956)

lemma oc_nc_2957: "oc_sub None 2957"
  by (oc_eval oc_nc_2957)

lemma oc_nc_2958: "oc_sub None 2958"
  by (oc_eval oc_nc_2958)

lemma oc_nc_2959: "oc_sub None 2959"
  by (oc_eval oc_nc_2959)

lemma upt_nc_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma sec_nc_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding upt_nc_184 .
  then show "oc_sub None j" using oc_nc_2944 oc_nc_2945 oc_nc_2946 oc_nc_2947 oc_nc_2948 oc_nc_2949 oc_nc_2950 oc_nc_2951 oc_nc_2952 oc_nc_2953 oc_nc_2954 oc_nc_2955 oc_nc_2956 oc_nc_2957 oc_nc_2958 oc_nc_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
