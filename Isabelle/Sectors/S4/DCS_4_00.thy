theory DCS_4_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_064: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 64) (-8)) (Float (int 64 + 1) (-8))"
  by eval

lemma dc_nc_064: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 64) (-8)) (Float (int 64 + 1) (-8))"
  by eval

lemma dc_c30_065: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 65) (-8)) (Float (int 65 + 1) (-8))"
  by eval

lemma dc_nc_065: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 65) (-8)) (Float (int 65 + 1) (-8))"
  by eval

lemma dc_c30_066: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 66) (-8)) (Float (int 66 + 1) (-8))"
  by eval

lemma dc_nc_066: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 66) (-8)) (Float (int 66 + 1) (-8))"
  by eval

lemma dc_c30_067: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 67) (-8)) (Float (int 67 + 1) (-8))"
  by eval

lemma dc_nc_067: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 67) (-8)) (Float (int 67 + 1) (-8))"
  by eval

end
