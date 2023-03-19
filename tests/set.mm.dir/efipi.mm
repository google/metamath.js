include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "c1.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "picn.mm"
include "efival.mm"
include "ax-mp.mm"
include "cc0.mm"
include "cospi.mm"
include "sinpi.mm"
include "oveq2i.mm"
include "it0e0.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "neg1cn.mm"
include "addid1i.mm"

theorem efipi



  assert |- ( exp ` ( _i x. _pi ) ) = -u 1

  proof
    ci
    cpi
    cmul
    co
    ce
    cfv
    #
    cpi
    ccos
    cfv
    #
    ci
    cpi
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    cneg
    #
    cpi
    cc
    wcel
    @0
    @4
    wceq
    picn
    cpi
    efival
    ax-mp
    @4
    @5
    cc0
    caddc
    co
    @5
    @1
    @5
    @3
    cc0
    caddc
    cospi
    @3
    ci
    cc0
    cmul
    co
    cc0
    @2
    cc0
    ci
    cmul
    sinpi
    oveq2i
    it0e0
    eqtri
    oveq12i
    @5
    neg1cn
    addid1i
    eqtri
    eqtri
end
