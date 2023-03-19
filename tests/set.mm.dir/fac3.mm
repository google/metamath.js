include "c3.mm"
include "cfa.mm"
include "cfv.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "c6.mm"
include "df-3.mm"
include "fveq2i.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "2nn0.mm"
include "facp1.mm"
include "ax-mp.mm"
include "fac2.mm"
include "2p1e3.mm"
include "oveq12i.mm"
include "2cn.mm"
include "3cn.mm"
include "mulcomi.mm"
include "3t2e6.mm"
include "3eqtri.mm"

theorem fac3



  assert |- ( ! ` 3 ) = 6

  proof
    c3
    cfa
    cfv
    c2
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    c2
    cfa
    cfv
    #
    @0
    cmul
    co
    #
    c6
    c3
    @0
    cfa
    df-3
    fveq2i
    c2
    cn0
    wcel
    @1
    @3
    wceq
    2nn0
    c2
    facp1
    ax-mp
    @3
    c2
    c3
    cmul
    co
    c3
    c2
    cmul
    co
    c6
    @2
    c2
    @0
    c3
    cmul
    fac2
    2p1e3
    oveq12i
    c2
    c3
    2cn
    3cn
    mulcomi
    3t2e6
    3eqtri
    3eqtri
end
