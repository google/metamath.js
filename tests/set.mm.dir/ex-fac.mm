include "c5.mm"
include "cfa.mm"
include "cfv.mm"
include "c4.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "cdc.mm"
include "cc0.mm"
include "df-5.mm"
include "fveq2i.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn0.mm"
include "facp1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fac4.mm"
include "4p1e5.mm"
include "oveq12i.mm"
include "5nn0.mm"
include "2nn0.mm"
include "eqid.mm"
include "0nn0.mm"
include "1nn0.mm"
include "5cn.mm"
include "2cn.mm"
include "5t2e10.mm"
include "mulcomli.mm"
include "addid2i.mm"
include "decaddi.mm"
include "4cn.mm"
include "5t4e20.mm"
include "decmul1c.mm"

theorem ex-fac



  assert |- ( ! ` 5 ) = ; ; 1 2 0

  proof
    c5
    cfa
    cfv
    #
    c4
    cfa
    cfv
    #
    c4
    c1
    caddc
    co
    #
    cmul
    co
    #
    c1
    c2
    cdc
    #
    cc0
    cdc
    #
    @0
    @2
    cfa
    cfv
    #
    @3
    c5
    @2
    cfa
    df-5
    fveq2i
    c4
    cn0
    wcel
    @6
    @3
    wceq
    4nn0
    c4
    facp1
    ax-mp
    eqtri
    @3
    c2
    c4
    cdc
    #
    c5
    cmul
    co
    @5
    @1
    @7
    @2
    c5
    cmul
    fac4
    4p1e5
    oveq12i
    c2
    c4
    @4
    cc0
    c5
    c2
    @7
    5nn0
    2nn0
    4nn0
    @7
    eqid
    0nn0
    2nn0
    c1
    cc0
    c2
    c2
    c5
    cmul
    co
    c2
    1nn0
    0nn0
    2nn0
    c5
    c2
    c1
    cc0
    cdc
    5cn
    2cn
    5t2e10
    mulcomli
    c2
    2cn
    addid2i
    decaddi
    c5
    c4
    c2
    cc0
    cdc
    5cn
    4cn
    5t4e20
    mulcomli
    decmul1c
    eqtri
    eqtri
end
