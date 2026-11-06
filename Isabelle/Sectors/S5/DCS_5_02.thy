theory DCS_5_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_088: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 88) (-8)) (Float (int 88 + 1) (-8))"
  by eval

lemma dc_nc_088: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 88) (-8)) (Float (int 88 + 1) (-8))"
  by eval

lemma dc_c30_089: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 89) (-8)) (Float (int 89 + 1) (-8))"
  by eval

lemma dc_nc_089: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 89) (-8)) (Float (int 89 + 1) (-8))"
  by eval

lemma dc_c30_090: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 90) (-8)) (Float (int 90 + 1) (-8))"
  by eval

lemma dc_nc_090: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 90) (-8)) (Float (int 90 + 1) (-8))"
  by eval

lemma dc_c30_091: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 91) (-8)) (Float (int 91 + 1) (-8))"
  by eval

lemma dc_nc_091: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 91) (-8)) (Float (int 91 + 1) (-8))"
  by eval

end
