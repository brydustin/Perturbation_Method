theory DCS_4_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_076: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 76) (-8)) (Float (int 76 + 1) (-8))"
  by eval

lemma dc_nc_076: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 76) (-8)) (Float (int 76 + 1) (-8))"
  by eval

lemma dc_c30_077: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 77) (-8)) (Float (int 77 + 1) (-8))"
  by eval

lemma dc_nc_077: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 77) (-8)) (Float (int 77 + 1) (-8))"
  by eval

lemma dc_c30_078: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 78) (-8)) (Float (int 78 + 1) (-8))"
  by eval

lemma dc_nc_078: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 78) (-8)) (Float (int 78 + 1) (-8))"
  by eval

lemma dc_c30_079: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 79) (-8)) (Float (int 79 + 1) (-8))"
  by eval

lemma dc_nc_079: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 79) (-8)) (Float (int 79 + 1) (-8))"
  by eval

end
