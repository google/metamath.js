include "cpnf.mm"
include "cmnf.mm"
include "pnfnemnf.mm"
include "necomi.mm"

theorem mnfnepnf



  assert |- -oo =/= +oo

  proof
    cpnf
    cmnf
    pnfnemnf
    necomi
end
