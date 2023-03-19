include "c2.mm"
include "c6.mm"
include "cop.mm"
include "csn.mm"
include "c3.mm"
include "c9.mm"
include "cun.mm"
include "ccnv.mm"
include "cpr.mm"
include "cnvun.mm"
include "cn.mm"
include "2nn.mm"
include "elexi.mm"
include "6nn.mm"
include "cnvsn.mm"
include "3nn.mm"
include "9nn.mm"
include "uneq12i.mm"
include "eqtri.mm"
include "df-pr.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"

theorem ex-cnv



  assert |- `' { <. 2 , 6 >. , <. 3 , 9 >. } = { <. 6 , 2 >. , <. 9 , 3 >. }

  proof
    c2
    c6
    cop
    #
    csn
    #
    c3
    c9
    cop
    #
    csn
    #
    cun
    #
    ccnv
    #
    c6
    c2
    cop
    #
    csn
    #
    c9
    c3
    cop
    #
    csn
    #
    cun
    #
    @0
    @2
    cpr
    #
    ccnv
    @6
    @8
    cpr
    @5
    @1
    ccnv
    #
    @3
    ccnv
    #
    cun
    @10
    @1
    @3
    cnvun
    @12
    @7
    @13
    @9
    c2
    c6
    c2
    cn
    2nn
    elexi
    c6
    cn
    6nn
    elexi
    cnvsn
    c3
    c9
    c3
    cn
    3nn
    elexi
    c9
    cn
    9nn
    elexi
    cnvsn
    uneq12i
    eqtri
    @11
    @4
    @0
    @2
    df-pr
    cnveqi
    @6
    @8
    df-pr
    3eqtr4i
end
