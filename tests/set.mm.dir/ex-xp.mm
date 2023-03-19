include "c1.mm"
include "c5.mm"
include "cpr.mm"
include "c2.mm"
include "c7.mm"
include "cxp.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "df-pr.mm"
include "xpeq12i.mm"
include "xpun.mm"
include "1ex.mm"
include "cn.mm"
include "2nn.mm"
include "elexi.mm"
include "xpsn.mm"
include "7nn.mm"
include "uneq12i.mm"
include "eqtr4i.mm"
include "5nn.mm"
include "3eqtri.mm"

theorem ex-xp



  assert |- ( { 1 , 5 } X. { 2 , 7 } ) = ( { <. 1 , 2 >. , <. 1 , 7 >. } u. { <. 5 , 2 >. , <. 5 , 7 >. } )

  proof
    c1
    c5
    cpr
    #
    c2
    c7
    cpr
    #
    cxp
    c1
    csn
    #
    c5
    csn
    #
    cun
    #
    c2
    csn
    #
    c7
    csn
    #
    cun
    #
    cxp
    @2
    @5
    cxp
    #
    @2
    @6
    cxp
    #
    cun
    #
    @3
    @5
    cxp
    #
    @3
    @6
    cxp
    #
    cun
    #
    cun
    c1
    c2
    cop
    #
    c1
    c7
    cop
    #
    cpr
    #
    c5
    c2
    cop
    #
    c5
    c7
    cop
    #
    cpr
    #
    cun
    @0
    @4
    @1
    @7
    c1
    c5
    df-pr
    c2
    c7
    df-pr
    xpeq12i
    @2
    @3
    @5
    @6
    xpun
    @10
    @16
    @13
    @19
    @10
    @14
    csn
    #
    @15
    csn
    #
    cun
    @16
    @8
    @20
    @9
    @21
    c1
    c2
    1ex
    c2
    cn
    2nn
    elexi
    #
    xpsn
    c1
    c7
    1ex
    c7
    cn
    7nn
    elexi
    #
    xpsn
    uneq12i
    @14
    @15
    df-pr
    eqtr4i
    @13
    @17
    csn
    #
    @18
    csn
    #
    cun
    @19
    @11
    @24
    @12
    @25
    c5
    c2
    c5
    cn
    5nn
    elexi
    #
    @22
    xpsn
    c5
    c7
    @26
    @23
    xpsn
    uneq12i
    @17
    @18
    df-pr
    eqtr4i
    uneq12i
    3eqtri
end
