include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "neghalfpire.mm"
include "rexri.mm"

theorem neghalfpirx



  assert |- -u ( _pi / 2 ) e. RR*

  proof
    cpi
    c2
    cdiv
    co
    cneg
    neghalfpire
    rexri
end
