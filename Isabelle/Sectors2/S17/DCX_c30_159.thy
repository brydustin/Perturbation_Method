theory DCX_c30_159
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2544: "dc_sub dc_b30 2544"
  by (dc_eval dc_c30_2544)

lemma dc_c30_2545: "dc_sub dc_b30 2545"
  by (dc_eval dc_c30_2545)

lemma dc_c30_2546: "dc_sub dc_b30 2546"
  by (dc_eval dc_c30_2546)

lemma dc_c30_2547: "dc_sub dc_b30 2547"
  by (dc_eval dc_c30_2547)

lemma dc_c30_2548: "dc_sub dc_b30 2548"
  by (dc_eval dc_c30_2548)

lemma dc_c30_2549: "dc_sub dc_b30 2549"
  by (dc_eval dc_c30_2549)

lemma dc_c30_2550: "dc_sub dc_b30 2550"
  by (dc_eval dc_c30_2550)

lemma dc_c30_2551: "dc_sub dc_b30 2551"
  by (dc_eval dc_c30_2551)

lemma dc_c30_2552: "dc_sub dc_b30 2552"
  by (dc_eval dc_c30_2552)

lemma dc_c30_2553: "dc_sub dc_b30 2553"
  by (dc_eval dc_c30_2553)

lemma dc_c30_2554: "dc_sub dc_b30 2554"
  by (dc_eval dc_c30_2554)

lemma dc_c30_2555: "dc_sub dc_b30 2555"
  by (dc_eval dc_c30_2555)

lemma dc_c30_2556: "dc_sub dc_b30 2556"
  by (dc_eval dc_c30_2556)

lemma dc_c30_2557: "dc_sub dc_b30 2557"
  by (dc_eval dc_c30_2557)

lemma dc_c30_2558: "dc_sub dc_b30 2558"
  by (dc_eval dc_c30_2558)

lemma dc_c30_2559: "dc_sub dc_b30 2559"
  by (dc_eval dc_c30_2559)

lemma upt_c30_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma sec_c30_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding upt_c30_159 .
  then show "dc_sub dc_b30 j" using dc_c30_2544 dc_c30_2545 dc_c30_2546 dc_c30_2547 dc_c30_2548 dc_c30_2549 dc_c30_2550 dc_c30_2551 dc_c30_2552 dc_c30_2553 dc_c30_2554 dc_c30_2555 dc_c30_2556 dc_c30_2557 dc_c30_2558 dc_c30_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
