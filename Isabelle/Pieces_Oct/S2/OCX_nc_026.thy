theory OCX_nc_026
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0416: "oc_sub None 416"
  by (oc_eval oc_nc_0416)

lemma oc_nc_0417: "oc_sub None 417"
  by (oc_eval oc_nc_0417)

lemma oc_nc_0418: "oc_sub None 418"
  by (oc_eval oc_nc_0418)

lemma oc_nc_0419: "oc_sub None 419"
  by (oc_eval oc_nc_0419)

lemma oc_nc_0420: "oc_sub None 420"
  by (oc_eval oc_nc_0420)

lemma oc_nc_0421: "oc_sub None 421"
  by (oc_eval oc_nc_0421)

lemma oc_nc_0422: "oc_sub None 422"
  by (oc_eval oc_nc_0422)

lemma oc_nc_0423: "oc_sub None 423"
  by (oc_eval oc_nc_0423)

lemma oc_nc_0424: "oc_sub None 424"
  by (oc_eval oc_nc_0424)

lemma oc_nc_0425: "oc_sub None 425"
  by (oc_eval oc_nc_0425)

lemma oc_nc_0426: "oc_sub None 426"
  by (oc_eval oc_nc_0426)

lemma oc_nc_0427: "oc_sub None 427"
  by (oc_eval oc_nc_0427)

lemma oc_nc_0428: "oc_sub None 428"
  by (oc_eval oc_nc_0428)

lemma oc_nc_0429: "oc_sub None 429"
  by (oc_eval oc_nc_0429)

lemma oc_nc_0430: "oc_sub None 430"
  by (oc_eval oc_nc_0430)

lemma oc_nc_0431: "oc_sub None 431"
  by (oc_eval oc_nc_0431)

lemma upt_nc_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma sec_nc_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding upt_nc_026 .
  then show "oc_sub None j" using oc_nc_0416 oc_nc_0417 oc_nc_0418 oc_nc_0419 oc_nc_0420 oc_nc_0421 oc_nc_0422 oc_nc_0423 oc_nc_0424 oc_nc_0425 oc_nc_0426 oc_nc_0427 oc_nc_0428 oc_nc_0429 oc_nc_0430 oc_nc_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
