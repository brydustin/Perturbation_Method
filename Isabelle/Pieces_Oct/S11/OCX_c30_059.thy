theory OCX_c30_059
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0944: "oc_sub oc_b30 944"
  by (oc_eval oc_c30_0944)

lemma oc_c30_0945: "oc_sub oc_b30 945"
  by (oc_eval oc_c30_0945)

lemma oc_c30_0946: "oc_sub oc_b30 946"
  by (oc_eval oc_c30_0946)

lemma oc_c30_0947: "oc_sub oc_b30 947"
  by (oc_eval oc_c30_0947)

lemma oc_c30_0948: "oc_sub oc_b30 948"
  by (oc_eval oc_c30_0948)

lemma oc_c30_0949: "oc_sub oc_b30 949"
  by (oc_eval oc_c30_0949)

lemma oc_c30_0950: "oc_sub oc_b30 950"
  by (oc_eval oc_c30_0950)

lemma oc_c30_0951: "oc_sub oc_b30 951"
  by (oc_eval oc_c30_0951)

lemma oc_c30_0952: "oc_sub oc_b30 952"
  by (oc_eval oc_c30_0952)

lemma oc_c30_0953: "oc_sub oc_b30 953"
  by (oc_eval oc_c30_0953)

lemma oc_c30_0954: "oc_sub oc_b30 954"
  by (oc_eval oc_c30_0954)

lemma oc_c30_0955: "oc_sub oc_b30 955"
  by (oc_eval oc_c30_0955)

lemma oc_c30_0956: "oc_sub oc_b30 956"
  by (oc_eval oc_c30_0956)

lemma oc_c30_0957: "oc_sub oc_b30 957"
  by (oc_eval oc_c30_0957)

lemma oc_c30_0958: "oc_sub oc_b30 958"
  by (oc_eval oc_c30_0958)

lemma oc_c30_0959: "oc_sub oc_b30 959"
  by (oc_eval oc_c30_0959)

lemma upt_c30_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma sec_c30_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding upt_c30_059 .
  then show "oc_sub oc_b30 j" using oc_c30_0944 oc_c30_0945 oc_c30_0946 oc_c30_0947 oc_c30_0948 oc_c30_0949 oc_c30_0950 oc_c30_0951 oc_c30_0952 oc_c30_0953 oc_c30_0954 oc_c30_0955 oc_c30_0956 oc_c30_0957 oc_c30_0958 oc_c30_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
