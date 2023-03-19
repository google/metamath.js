include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ccos.mm"
include "cc0.mm"
include "sinhalfpilem.mm"
include "simpri.mm"

theorem coshalfpi



  assert |- ( cos ` ( _pi / 2 ) ) = 0

  proof
    cpi
    c2
    cdiv
    co
    #
    csin
    cfv
    c1
    wceq
    @0
    ccos
    cfv
    cc0
    wceq
    sinhalfpilem
    simpri
end
