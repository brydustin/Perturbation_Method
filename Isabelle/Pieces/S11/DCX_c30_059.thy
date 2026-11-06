theory DCX_c30_059
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0944: "dc_sub dc_b30 944"
  by (dc_eval dc_c30_0944)

lemma dc_c30_0945: "dc_sub dc_b30 945"
  by (dc_eval dc_c30_0945)

lemma dc_c30_0946: "dc_sub dc_b30 946"
  by (dc_eval dc_c30_0946)

lemma dc_c30_0947: "dc_sub dc_b30 947"
  by (dc_eval dc_c30_0947)

lemma dc_c30_0948: "dc_sub dc_b30 948"
  by (dc_eval dc_c30_0948)

lemma dc_c30_0949: "dc_sub dc_b30 949"
  by (dc_eval dc_c30_0949)

lemma dc_c30_0950: "dc_sub dc_b30 950"
  by (dc_eval dc_c30_0950)

lemma dc_c30_0951: "dc_sub dc_b30 951"
  by (dc_eval dc_c30_0951)

lemma dc_c30_0952: "dc_sub dc_b30 952"
  by (dc_eval dc_c30_0952)

lemma dc_c30_0953: "dc_sub dc_b30 953"
  by (dc_eval dc_c30_0953)

lemma dc_c30_0954: "dc_sub dc_b30 954"
  by (dc_eval dc_c30_0954)

lemma dc_c30_0955: "dc_sub dc_b30 955"
  by (dc_eval dc_c30_0955)

lemma dc_c30_0956: "dc_sub dc_b30 956"
  by (dc_eval dc_c30_0956)

lemma dc_c30_0957: "dc_sub dc_b30 957"
  by (dc_eval dc_c30_0957)

lemma dc_c30_0958: "dc_sub dc_b30 958"
  by (dc_eval dc_c30_0958)

lemma dc_c30_0959: "dc_sub dc_b30 959"
  by (dc_eval dc_c30_0959)

lemma upt_c30_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma sec_c30_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding upt_c30_059 .
  then show "dc_sub dc_b30 j" using dc_c30_0944 dc_c30_0945 dc_c30_0946 dc_c30_0947 dc_c30_0948 dc_c30_0949 dc_c30_0950 dc_c30_0951 dc_c30_0952 dc_c30_0953 dc_c30_0954 dc_c30_0955 dc_c30_0956 dc_c30_0957 dc_c30_0958 dc_c30_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
