theory OCX_nc_059
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0944: "oc_sub None 944"
  by (oc_eval oc_nc_0944)

lemma oc_nc_0945: "oc_sub None 945"
  by (oc_eval oc_nc_0945)

lemma oc_nc_0946: "oc_sub None 946"
  by (oc_eval oc_nc_0946)

lemma oc_nc_0947: "oc_sub None 947"
  by (oc_eval oc_nc_0947)

lemma oc_nc_0948: "oc_sub None 948"
  by (oc_eval oc_nc_0948)

lemma oc_nc_0949: "oc_sub None 949"
  by (oc_eval oc_nc_0949)

lemma oc_nc_0950: "oc_sub None 950"
  by (oc_eval oc_nc_0950)

lemma oc_nc_0951: "oc_sub None 951"
  by (oc_eval oc_nc_0951)

lemma oc_nc_0952: "oc_sub None 952"
  by (oc_eval oc_nc_0952)

lemma oc_nc_0953: "oc_sub None 953"
  by (oc_eval oc_nc_0953)

lemma oc_nc_0954: "oc_sub None 954"
  by (oc_eval oc_nc_0954)

lemma oc_nc_0955: "oc_sub None 955"
  by (oc_eval oc_nc_0955)

lemma oc_nc_0956: "oc_sub None 956"
  by (oc_eval oc_nc_0956)

lemma oc_nc_0957: "oc_sub None 957"
  by (oc_eval oc_nc_0957)

lemma oc_nc_0958: "oc_sub None 958"
  by (oc_eval oc_nc_0958)

lemma oc_nc_0959: "oc_sub None 959"
  by (oc_eval oc_nc_0959)

lemma upt_nc_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma sec_nc_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding upt_nc_059 .
  then show "oc_sub None j" using oc_nc_0944 oc_nc_0945 oc_nc_0946 oc_nc_0947 oc_nc_0948 oc_nc_0949 oc_nc_0950 oc_nc_0951 oc_nc_0952 oc_nc_0953 oc_nc_0954 oc_nc_0955 oc_nc_0956 oc_nc_0957 oc_nc_0958 oc_nc_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
