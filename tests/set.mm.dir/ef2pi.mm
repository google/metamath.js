include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "efival.mm"
include "ax-mp.mm"
include "cc0.mm"
include "cos2pi.mm"
include "sin2pi.mm"
include "oveq2i.mm"
include "it0e0.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "1p0e1.mm"

theorem ef2pi



  assert |- ( exp ` ( _i x. ( 2 x. _pi ) ) ) = 1

  proof
    ci
    c2
    cpi
    cmul
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
    c1
    @0
    cc
    wcel
    @1
    @5
    wceq
    c2
    cpi
    2cn
    picn
    mulcli
    @0
    efival
    ax-mp
    @5
    c1
    cc0
    caddc
    co
    c1
    @2
    c1
    @4
    cc0
    caddc
    cos2pi
    @4
    ci
    cc0
    cmul
    co
    cc0
    @3
    cc0
    ci
    cmul
    sin2pi
    oveq2i
    it0e0
    eqtri
    oveq12i
    1p0e1
    eqtri
    eqtri
end
