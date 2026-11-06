theory DCX_nc_159
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2544: "dc_sub None 2544"
  by (dc_eval dc_nc_2544)

lemma dc_nc_2545: "dc_sub None 2545"
  by (dc_eval dc_nc_2545)

lemma dc_nc_2546: "dc_sub None 2546"
  by (dc_eval dc_nc_2546)

lemma dc_nc_2547: "dc_sub None 2547"
  by (dc_eval dc_nc_2547)

lemma dc_nc_2548: "dc_sub None 2548"
  by (dc_eval dc_nc_2548)

lemma dc_nc_2549: "dc_sub None 2549"
  by (dc_eval dc_nc_2549)

lemma dc_nc_2550: "dc_sub None 2550"
  by (dc_eval dc_nc_2550)

lemma dc_nc_2551: "dc_sub None 2551"
  by (dc_eval dc_nc_2551)

lemma dc_nc_2552: "dc_sub None 2552"
  by (dc_eval dc_nc_2552)

lemma dc_nc_2553: "dc_sub None 2553"
  by (dc_eval dc_nc_2553)

lemma dc_nc_2554: "dc_sub None 2554"
  by (dc_eval dc_nc_2554)

lemma dc_nc_2555: "dc_sub None 2555"
  by (dc_eval dc_nc_2555)

lemma dc_nc_2556: "dc_sub None 2556"
  by (dc_eval dc_nc_2556)

lemma dc_nc_2557: "dc_sub None 2557"
  by (dc_eval dc_nc_2557)

lemma dc_nc_2558: "dc_sub None 2558"
  by (dc_eval dc_nc_2558)

lemma dc_nc_2559: "dc_sub None 2559"
  by (dc_eval dc_nc_2559)

lemma upt_nc_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma sec_nc_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding upt_nc_159 .
  then show "dc_sub None j" using dc_nc_2544 dc_nc_2545 dc_nc_2546 dc_nc_2547 dc_nc_2548 dc_nc_2549 dc_nc_2550 dc_nc_2551 dc_nc_2552 dc_nc_2553 dc_nc_2554 dc_nc_2555 dc_nc_2556 dc_nc_2557 dc_nc_2558 dc_nc_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
