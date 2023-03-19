include "ci.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "ce.mm"
include "cfv.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "picn.mm"
include "halfcl.mm"
include "efival.mm"
include "mp2b.mm"
include "cc0.mm"
include "coshalfpi.mm"
include "c1.mm"
include "sinhalfpi.mm"
include "oveq2i.mm"
include "ax-icn.mm"
include "mulid1i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "addid2i.mm"

theorem efhalfpi



  assert |- ( exp ` ( _i x. ( _pi / 2 ) ) ) = _i

  proof
    ci
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    ce
    cfv
    #
    @0
    ccos
    cfv
    #
    ci
    @0
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    ci
    cpi
    cc
    wcel
    @0
    cc
    wcel
    @1
    @5
    wceq
    picn
    cpi
    halfcl
    @0
    efival
    mp2b
    @5
    cc0
    ci
    caddc
    co
    ci
    @2
    cc0
    @4
    ci
    caddc
    coshalfpi
    @4
    ci
    c1
    cmul
    co
    ci
    @3
    c1
    ci
    cmul
    sinhalfpi
    oveq2i
    ci
    ax-icn
    mulid1i
    eqtri
    oveq12i
    ci
    ax-icn
    addid2i
    eqtri
    eqtri
end
