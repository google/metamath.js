include "c2.mm"
include "cpi.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "ccos.mm"
include "cfv.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcli.mm"
include "cos2t.mm"
include "ax-mp.mm"
include "divcan2i.mm"
include "fveq2i.mm"
include "cc0.mm"
include "coshalfpi.mm"
include "oveq1i.mm"
include "sq0.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "2t0e0.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "3eqtr3i.mm"

theorem cospi



  assert |- ( cos ` _pi ) = -u 1

  proof
    c2
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    ccos
    cfv
    #
    c2
    @0
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cmin
    co
    #
    cpi
    ccos
    cfv
    c1
    cneg
    #
    @0
    cc
    wcel
    @2
    @6
    wceq
    cpi
    c2
    picn
    2cn
    2ne0
    divcli
    @0
    cos2t
    ax-mp
    @1
    cpi
    ccos
    cpi
    c2
    picn
    2cn
    2ne0
    divcan2i
    fveq2i
    @6
    cc0
    c1
    cmin
    co
    @7
    @5
    cc0
    c1
    cmin
    @5
    c2
    cc0
    cmul
    co
    cc0
    @4
    cc0
    c2
    cmul
    @4
    cc0
    c2
    cexp
    co
    cc0
    @3
    cc0
    c2
    cexp
    coshalfpi
    oveq1i
    sq0
    eqtri
    oveq2i
    2t0e0
    eqtri
    oveq1i
    c1
    df-neg
    eqtr4i
    3eqtr3i
end
