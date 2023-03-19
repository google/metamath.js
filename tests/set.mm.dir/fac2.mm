include "c2.mm"
include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-2.mm"
include "fveq2i.mm"
include "cmul.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "1nn0.mm"
include "facp1.mm"
include "ax-mp.mm"
include "fac1.mm"
include "1p1e2.mm"
include "oveq12i.mm"
include "2cn.mm"
include "mulid2i.mm"
include "eqtri.mm"

theorem fac2



  assert |- ( ! ` 2 ) = 2

  proof
    c2
    cfa
    cfv
    c1
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    c2
    c2
    @0
    cfa
    df-2
    fveq2i
    @1
    c1
    cfa
    cfv
    #
    @0
    cmul
    co
    #
    c2
    c1
    cn0
    wcel
    @1
    @3
    wceq
    1nn0
    c1
    facp1
    ax-mp
    @3
    c1
    c2
    cmul
    co
    c2
    @2
    c1
    @0
    c2
    cmul
    fac1
    1p1e2
    oveq12i
    c2
    2cn
    mulid2i
    eqtri
    eqtri
    eqtri
end
