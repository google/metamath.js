include "c3.mm"
include "cprmo.mm"
include "cfv.mm"
include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cif.mm"
include "c6.mm"
include "cn.mm"
include "wceq.mm"
include "3nn.mm"
include "prmonn2.mm"
include "ax-mp.mm"
include "3prm.mm"
include "iftruei.mm"
include "c2.mm"
include "3m1e2.mm"
include "fveq2i.mm"
include "prmo2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "3cn.mm"
include "2cn.mm"
include "3t2e6.mm"
include "mulcomli.mm"

theorem prmo3



  assert |- ( #p ` 3 ) = 6

  proof
    c3
    cprmo
    cfv
    #
    c3
    cprime
    wcel
    #
    c3
    c1
    cmin
    co
    #
    cprmo
    cfv
    #
    c3
    cmul
    co
    #
    @3
    cif
    #
    c6
    c3
    cn
    wcel
    @0
    @5
    wceq
    3nn
    c3
    prmonn2
    ax-mp
    @5
    @4
    c6
    @1
    @4
    @3
    3prm
    iftruei
    @4
    c2
    c3
    cmul
    co
    c6
    @3
    c2
    c3
    cmul
    @3
    c2
    cprmo
    cfv
    c2
    @2
    c2
    cprmo
    3m1e2
    fveq2i
    prmo2
    eqtri
    oveq1i
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    eqtri
    eqtri
    eqtri
end
