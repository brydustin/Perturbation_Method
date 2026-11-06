theory DCS_0_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_004: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 4) (-8)) (Float (int 4 + 1) (-8))"
  by eval

lemma dc_nc_004: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 4) (-8)) (Float (int 4 + 1) (-8))"
  by eval

lemma dc_c30_005: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 5) (-8)) (Float (int 5 + 1) (-8))"
  by eval

lemma dc_nc_005: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 5) (-8)) (Float (int 5 + 1) (-8))"
  by eval

lemma dc_c30_006: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 6) (-8)) (Float (int 6 + 1) (-8))"
  by eval

lemma dc_nc_006: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 6) (-8)) (Float (int 6 + 1) (-8))"
  by eval

lemma dc_c30_007: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 7) (-8)) (Float (int 7 + 1) (-8))"
  by eval

lemma dc_nc_007: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 7) (-8)) (Float (int 7 + 1) (-8))"
  by eval

end
