include "c6.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c3.mm"
include "cc0.mm"
include "cdc.mm"
include "cprime.mm"
include "wcel.mm"
include "cmul.mm"
include "cif.mm"
include "cn.mm"
include "wceq.mm"
include "6nn.mm"
include "prmonn2.mm"
include "ax-mp.mm"
include "6nprm.mm"
include "iffalsei.mm"
include "eqtri.mm"
include "c5.mm"
include "caddc.mm"
include "5p1e6.mm"
include "6cn.mm"
include "ax-1cn.mm"
include "5cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "fveq2i.mm"
include "prmo5.mm"

theorem prmo6



  assert |- ( #p ` 6 ) = ; 3 0

  proof
    c6
    cprmo
    cfv
    #
    c6
    c1
    cmin
    co
    #
    cprmo
    cfv
    #
    c3
    cc0
    cdc
    #
    @0
    c6
    cprime
    wcel
    #
    @2
    c6
    cmul
    co
    #
    @2
    cif
    #
    @2
    c6
    cn
    wcel
    @0
    @6
    wceq
    6nn
    c6
    prmonn2
    ax-mp
    @4
    @5
    @2
    6nprm
    iffalsei
    eqtri
    @2
    c5
    cprmo
    cfv
    @3
    @1
    c5
    cprmo
    @1
    c5
    wceq
    c5
    c1
    caddc
    co
    c6
    wceq
    5p1e6
    c6
    c1
    c5
    6cn
    ax-1cn
    5cn
    subadd2i
    mpbir
    fveq2i
    prmo5
    eqtri
    eqtri
end
