include "cmnf.mm"
include "cr.mm"
include "mnfnre.mm"
include "neli.mm"

theorem mnfnre2



  assert |- -. -oo e. RR

  proof
    cmnf
    cr
    mnfnre
    neli
end
