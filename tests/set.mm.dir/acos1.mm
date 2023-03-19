include "c1.mm"
include "cacos.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "casin.mm"
include "cmin.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "acosval.mm"
include "ax-mp.mm"
include "asin1.mm"
include "oveq2i.mm"
include "picn.mm"
include "halfcl.mm"
include "subidi.mm"
include "3eqtri.mm"

theorem acos1



  assert |- ( arccos ` 1 ) = 0

  proof
    c1
    cacos
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    c1
    casin
    cfv
    #
    cmin
    co
    #
    @1
    @1
    cmin
    co
    cc0
    c1
    cc
    wcel
    @0
    @3
    wceq
    ax-1cn
    c1
    acosval
    ax-mp
    @2
    @1
    @1
    cmin
    asin1
    oveq2i
    @1
    cpi
    cc
    wcel
    @1
    cc
    wcel
    picn
    cpi
    halfcl
    ax-mp
    subidi
    3eqtri
end
