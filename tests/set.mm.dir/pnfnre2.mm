include "cpnf.mm"
include "cr.mm"
include "pnfnre.mm"
include "neli.mm"

theorem pnfnre2



  assert |- -. +oo e. RR

  proof
    cpnf
    cr
    pnfnre
    neli
end
