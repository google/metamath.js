include "c3.mm"
include "c2.mm"
include "c7.mm"
include "cdc.mm"
include "3nn0.mm"
include "2nn0.mm"
include "2p1e3.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c9.mm"
include "sq3.mm"
include "oveq1i.mm"
include "9t3e27.mm"
include "eqtri.mm"
include "numexpp1.mm"

theorem 3exp3



  assert |- ( 3 ^ 3 ) = ; 2 7

  proof
    c3
    c2
    c7
    cdc
    #
    c2
    c3
    3nn0
    2nn0
    2p1e3
    c3
    c2
    cexp
    co
    #
    c3
    cmul
    co
    c9
    c3
    cmul
    co
    @0
    @1
    c9
    c3
    cmul
    sq3
    oveq1i
    9t3e27
    eqtri
    numexpp1
end
