theory OCX_c30_159
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2544: "oc_sub oc_b30 2544"
  by (oc_eval oc_c30_2544)

lemma oc_c30_2545: "oc_sub oc_b30 2545"
  by (oc_eval oc_c30_2545)

lemma oc_c30_2546: "oc_sub oc_b30 2546"
  by (oc_eval oc_c30_2546)

lemma oc_c30_2547: "oc_sub oc_b30 2547"
  by (oc_eval oc_c30_2547)

lemma oc_c30_2548: "oc_sub oc_b30 2548"
  by (oc_eval oc_c30_2548)

lemma oc_c30_2549: "oc_sub oc_b30 2549"
  by (oc_eval oc_c30_2549)

lemma oc_c30_2550: "oc_sub oc_b30 2550"
  by (oc_eval oc_c30_2550)

lemma oc_c30_2551: "oc_sub oc_b30 2551"
  by (oc_eval oc_c30_2551)

lemma oc_c30_2552: "oc_sub oc_b30 2552"
  by (oc_eval oc_c30_2552)

lemma oc_c30_2553: "oc_sub oc_b30 2553"
  by (oc_eval oc_c30_2553)

lemma oc_c30_2554: "oc_sub oc_b30 2554"
  by (oc_eval oc_c30_2554)

lemma oc_c30_2555: "oc_sub oc_b30 2555"
  by (oc_eval oc_c30_2555)

lemma oc_c30_2556: "oc_sub oc_b30 2556"
  by (oc_eval oc_c30_2556)

lemma oc_c30_2557: "oc_sub oc_b30 2557"
  by (oc_eval oc_c30_2557)

lemma oc_c30_2558: "oc_sub oc_b30 2558"
  by (oc_eval oc_c30_2558)

lemma oc_c30_2559: "oc_sub oc_b30 2559"
  by (oc_eval oc_c30_2559)

lemma upt_c30_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma sec_c30_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding upt_c30_159 .
  then show "oc_sub oc_b30 j" using oc_c30_2544 oc_c30_2545 oc_c30_2546 oc_c30_2547 oc_c30_2548 oc_c30_2549 oc_c30_2550 oc_c30_2551 oc_c30_2552 oc_c30_2553 oc_c30_2554 oc_c30_2555 oc_c30_2556 oc_c30_2557 oc_c30_2558 oc_c30_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
