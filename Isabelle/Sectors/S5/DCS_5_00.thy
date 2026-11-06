theory DCS_5_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_080: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 80) (-8)) (Float (int 80 + 1) (-8))"
  by eval

lemma dc_nc_080: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 80) (-8)) (Float (int 80 + 1) (-8))"
  by eval

lemma dc_c30_081: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 81) (-8)) (Float (int 81 + 1) (-8))"
  by eval

lemma dc_nc_081: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 81) (-8)) (Float (int 81 + 1) (-8))"
  by eval

lemma dc_c30_082: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 82) (-8)) (Float (int 82 + 1) (-8))"
  by eval

lemma dc_nc_082: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 82) (-8)) (Float (int 82 + 1) (-8))"
  by eval

lemma dc_c30_083: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 83) (-8)) (Float (int 83 + 1) (-8))"
  by eval

lemma dc_nc_083: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 83) (-8)) (Float (int 83 + 1) (-8))"
  by eval

end
