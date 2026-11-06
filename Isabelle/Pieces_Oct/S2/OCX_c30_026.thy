theory OCX_c30_026
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0416: "oc_sub oc_b30 416"
  by (oc_eval oc_c30_0416)

lemma oc_c30_0417: "oc_sub oc_b30 417"
  by (oc_eval oc_c30_0417)

lemma oc_c30_0418: "oc_sub oc_b30 418"
  by (oc_eval oc_c30_0418)

lemma oc_c30_0419: "oc_sub oc_b30 419"
  by (oc_eval oc_c30_0419)

lemma oc_c30_0420: "oc_sub oc_b30 420"
  by (oc_eval oc_c30_0420)

lemma oc_c30_0421: "oc_sub oc_b30 421"
  by (oc_eval oc_c30_0421)

lemma oc_c30_0422: "oc_sub oc_b30 422"
  by (oc_eval oc_c30_0422)

lemma oc_c30_0423: "oc_sub oc_b30 423"
  by (oc_eval oc_c30_0423)

lemma oc_c30_0424: "oc_sub oc_b30 424"
  by (oc_eval oc_c30_0424)

lemma oc_c30_0425: "oc_sub oc_b30 425"
  by (oc_eval oc_c30_0425)

lemma oc_c30_0426: "oc_sub oc_b30 426"
  by (oc_eval oc_c30_0426)

lemma oc_c30_0427: "oc_sub oc_b30 427"
  by (oc_eval oc_c30_0427)

lemma oc_c30_0428: "oc_sub oc_b30 428"
  by (oc_eval oc_c30_0428)

lemma oc_c30_0429: "oc_sub oc_b30 429"
  by (oc_eval oc_c30_0429)

lemma oc_c30_0430: "oc_sub oc_b30 430"
  by (oc_eval oc_c30_0430)

lemma oc_c30_0431: "oc_sub oc_b30 431"
  by (oc_eval oc_c30_0431)

lemma upt_c30_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma sec_c30_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding upt_c30_026 .
  then show "oc_sub oc_b30 j" using oc_c30_0416 oc_c30_0417 oc_c30_0418 oc_c30_0419 oc_c30_0420 oc_c30_0421 oc_c30_0422 oc_c30_0423 oc_c30_0424 oc_c30_0425 oc_c30_0426 oc_c30_0427 oc_c30_0428 oc_c30_0429 oc_c30_0430 oc_c30_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
