theory DCX_nc_059
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0944: "dc_sub None 944"
  by (dc_eval dc_nc_0944)

lemma dc_nc_0945: "dc_sub None 945"
  by (dc_eval dc_nc_0945)

lemma dc_nc_0946: "dc_sub None 946"
  by (dc_eval dc_nc_0946)

lemma dc_nc_0947: "dc_sub None 947"
  by (dc_eval dc_nc_0947)

lemma dc_nc_0948: "dc_sub None 948"
  by (dc_eval dc_nc_0948)

lemma dc_nc_0949: "dc_sub None 949"
  by (dc_eval dc_nc_0949)

lemma dc_nc_0950: "dc_sub None 950"
  by (dc_eval dc_nc_0950)

lemma dc_nc_0951: "dc_sub None 951"
  by (dc_eval dc_nc_0951)

lemma dc_nc_0952: "dc_sub None 952"
  by (dc_eval dc_nc_0952)

lemma dc_nc_0953: "dc_sub None 953"
  by (dc_eval dc_nc_0953)

lemma dc_nc_0954: "dc_sub None 954"
  by (dc_eval dc_nc_0954)

lemma dc_nc_0955: "dc_sub None 955"
  by (dc_eval dc_nc_0955)

lemma dc_nc_0956: "dc_sub None 956"
  by (dc_eval dc_nc_0956)

lemma dc_nc_0957: "dc_sub None 957"
  by (dc_eval dc_nc_0957)

lemma dc_nc_0958: "dc_sub None 958"
  by (dc_eval dc_nc_0958)

lemma dc_nc_0959: "dc_sub None 959"
  by (dc_eval dc_nc_0959)

lemma upt_nc_059: "[944..<960] = [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]"
  by (simp add: upt_rec)

lemma sec_nc_059: "\<forall>j\<in>{16 * 59..<16 * 59 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 59..<16 * 59 + 16}"
  then have "j \<in> set [944..<960]" unfolding set_upt by simp
  then have "j \<in> set [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]" unfolding upt_nc_059 .
  then show "dc_sub None j" using dc_nc_0944 dc_nc_0945 dc_nc_0946 dc_nc_0947 dc_nc_0948 dc_nc_0949 dc_nc_0950 dc_nc_0951 dc_nc_0952 dc_nc_0953 dc_nc_0954 dc_nc_0955 dc_nc_0956 dc_nc_0957 dc_nc_0958 dc_nc_0959
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
