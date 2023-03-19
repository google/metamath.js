include "c4.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c6.mm"
include "cprime.mm"
include "wcel.mm"
include "cmul.mm"
include "cif.mm"
include "cn.mm"
include "wceq.mm"
include "4nn.mm"
include "prmonn2.mm"
include "ax-mp.mm"
include "4nprm.mm"
include "iffalsei.mm"
include "eqtri.mm"
include "c3.mm"
include "caddc.mm"
include "3p1e4.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "fveq2i.mm"
include "prmo3.mm"

theorem prmo4



  assert |- ( #p ` 4 ) = 6

  proof
    c4
    cprmo
    cfv
    #
    c4
    c1
    cmin
    co
    #
    cprmo
    cfv
    #
    c6
    @0
    c4
    cprime
    wcel
    #
    @2
    c4
    cmul
    co
    #
    @2
    cif
    #
    @2
    c4
    cn
    wcel
    @0
    @5
    wceq
    4nn
    c4
    prmonn2
    ax-mp
    @3
    @4
    @2
    4nprm
    iffalsei
    eqtri
    @2
    c3
    cprmo
    cfv
    c6
    @1
    c3
    cprmo
    @1
    c3
    wceq
    c3
    c1
    caddc
    co
    c4
    wceq
    3p1e4
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    subadd2i
    mpbir
    fveq2i
    prmo3
    eqtri
    eqtri
end
