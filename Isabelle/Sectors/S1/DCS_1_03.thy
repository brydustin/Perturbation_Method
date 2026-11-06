theory DCS_1_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_028: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 28) (-8)) (Float (int 28 + 1) (-8))"
  by eval

lemma dc_nc_028: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 28) (-8)) (Float (int 28 + 1) (-8))"
  by eval

lemma dc_c30_029: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 29) (-8)) (Float (int 29 + 1) (-8))"
  by eval

lemma dc_nc_029: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 29) (-8)) (Float (int 29 + 1) (-8))"
  by eval

lemma dc_c30_030: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 30) (-8)) (Float (int 30 + 1) (-8))"
  by eval

lemma dc_nc_030: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 30) (-8)) (Float (int 30 + 1) (-8))"
  by eval

lemma dc_c30_031: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 31) (-8)) (Float (int 31 + 1) (-8))"
  by eval

lemma dc_nc_031: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 31) (-8)) (Float (int 31 + 1) (-8))"
  by eval

end
