theory OCX_c30_184
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2944: "oc_sub oc_b30 2944"
  by (oc_eval oc_c30_2944)

lemma oc_c30_2945: "oc_sub oc_b30 2945"
  by (oc_eval oc_c30_2945)

lemma oc_c30_2946: "oc_sub oc_b30 2946"
  by (oc_eval oc_c30_2946)

lemma oc_c30_2947: "oc_sub oc_b30 2947"
  by (oc_eval oc_c30_2947)

lemma oc_c30_2948: "oc_sub oc_b30 2948"
  by (oc_eval oc_c30_2948)

lemma oc_c30_2949: "oc_sub oc_b30 2949"
  by (oc_eval oc_c30_2949)

lemma oc_c30_2950: "oc_sub oc_b30 2950"
  by (oc_eval oc_c30_2950)

lemma oc_c30_2951: "oc_sub oc_b30 2951"
  by (oc_eval oc_c30_2951)

lemma oc_c30_2952: "oc_sub oc_b30 2952"
  by (oc_eval oc_c30_2952)

lemma oc_c30_2953: "oc_sub oc_b30 2953"
  by (oc_eval oc_c30_2953)

lemma oc_c30_2954: "oc_sub oc_b30 2954"
  by (oc_eval oc_c30_2954)

lemma oc_c30_2955: "oc_sub oc_b30 2955"
  by (oc_eval oc_c30_2955)

lemma oc_c30_2956: "oc_sub oc_b30 2956"
  by (oc_eval oc_c30_2956)

lemma oc_c30_2957: "oc_sub oc_b30 2957"
  by (oc_eval oc_c30_2957)

lemma oc_c30_2958: "oc_sub oc_b30 2958"
  by (oc_eval oc_c30_2958)

lemma oc_c30_2959: "oc_sub oc_b30 2959"
  by (oc_eval oc_c30_2959)

lemma upt_c30_184: "[2944..<2960] = [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]"
  by (simp add: upt_rec)

lemma sec_c30_184: "\<forall>j\<in>{16 * 184..<16 * 184 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 184..<16 * 184 + 16}"
  then have "j \<in> set [2944..<2960]" unfolding set_upt by simp
  then have "j \<in> set [2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959]" unfolding upt_c30_184 .
  then show "oc_sub oc_b30 j" using oc_c30_2944 oc_c30_2945 oc_c30_2946 oc_c30_2947 oc_c30_2948 oc_c30_2949 oc_c30_2950 oc_c30_2951 oc_c30_2952 oc_c30_2953 oc_c30_2954 oc_c30_2955 oc_c30_2956 oc_c30_2957 oc_c30_2958 oc_c30_2959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
