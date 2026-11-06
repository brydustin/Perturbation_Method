theory DCS_3_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_052: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 52) (-8)) (Float (int 52 + 1) (-8))"
  by eval

lemma dc_nc_052: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 52) (-8)) (Float (int 52 + 1) (-8))"
  by eval

lemma dc_c30_053: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 53) (-8)) (Float (int 53 + 1) (-8))"
  by eval

lemma dc_nc_053: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 53) (-8)) (Float (int 53 + 1) (-8))"
  by eval

lemma dc_c30_054: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 54) (-8)) (Float (int 54 + 1) (-8))"
  by eval

lemma dc_nc_054: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 54) (-8)) (Float (int 54 + 1) (-8))"
  by eval

lemma dc_c30_055: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 55) (-8)) (Float (int 55 + 1) (-8))"
  by eval

lemma dc_nc_055: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 55) (-8)) (Float (int 55 + 1) (-8))"
  by eval

end
