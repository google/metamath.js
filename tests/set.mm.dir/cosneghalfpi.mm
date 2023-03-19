include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "halfpire.mm"
include "recni.mm"
include "cosneg.mm"
include "ax-mp.mm"
include "coshalfpi.mm"
include "eqtri.mm"

theorem cosneghalfpi



  assert |- ( cos ` -u ( _pi / 2 ) ) = 0

  proof
    cpi
    c2
    cdiv
    co
    #
    cneg
    ccos
    cfv
    #
    @0
    ccos
    cfv
    #
    cc0
    @0
    cc
    wcel
    @1
    @2
    wceq
    @0
    halfpire
    recni
    @0
    cosneg
    ax-mp
    coshalfpi
    eqtri
end
