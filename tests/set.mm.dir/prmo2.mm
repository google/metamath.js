include "c2.mm"
include "cprmo.mm"
include "cfv.mm"
include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cif.mm"
include "cn.mm"
include "wceq.mm"
include "2nn.mm"
include "prmonn2.mm"
include "ax-mp.mm"
include "2prm.mm"
include "iftruei.mm"
include "2m1e1.mm"
include "fveq2i.mm"
include "prmo1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "2cn.mm"
include "mulid2i.mm"

theorem prmo2



  assert |- ( #p ` 2 ) = 2

  proof
    c2
    cprmo
    cfv
    #
    c2
    cprime
    wcel
    #
    c2
    c1
    cmin
    co
    #
    cprmo
    cfv
    #
    c2
    cmul
    co
    #
    @3
    cif
    #
    c2
    c2
    cn
    wcel
    @0
    @5
    wceq
    2nn
    c2
    prmonn2
    ax-mp
    @5
    @4
    c2
    @1
    @4
    @3
    2prm
    iftruei
    @4
    c1
    c2
    cmul
    co
    c2
    @3
    c1
    c2
    cmul
    @3
    c1
    cprmo
    cfv
    c1
    @2
    c1
    cprmo
    2m1e1
    fveq2i
    prmo1
    eqtri
    oveq1i
    c2
    2cn
    mulid2i
    eqtri
    eqtri
    eqtri
end
