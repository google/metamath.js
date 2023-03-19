include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "picn.mm"
include "cos2t.mm"
include "ax-mp.mm"
include "cneg.mm"
include "cospi.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "sqneg.mm"
include "sq1.mm"
include "3eqtri.mm"
include "oveq2i.mm"
include "2t1e2.mm"
include "eqtri.mm"
include "2m1e1.mm"

theorem cos2pi



  assert |- ( cos ` ( 2 x. _pi ) ) = 1

  proof
    c2
    cpi
    cmul
    co
    ccos
    cfv
    #
    c2
    cpi
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
    c2
    c1
    cmin
    co
    c1
    cpi
    cc
    wcel
    @0
    @4
    wceq
    picn
    cpi
    cos2t
    ax-mp
    @3
    c2
    c1
    cmin
    @3
    c2
    c1
    cmul
    co
    c2
    @2
    c1
    c2
    cmul
    @2
    c1
    cneg
    #
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    c1
    @1
    @5
    c2
    cexp
    cospi
    oveq1i
    c1
    cc
    wcel
    @6
    @7
    wceq
    ax-1cn
    c1
    sqneg
    ax-mp
    sq1
    3eqtri
    oveq2i
    2t1e2
    eqtri
    oveq1i
    2m1e1
    3eqtri
end
