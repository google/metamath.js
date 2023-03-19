include "c1.mm"
include "c3.mm"
include "cpr.mm"
include "c8.mm"
include "cuni.mm"
include "cun.mm"
include "ctp.mm"
include "prex.mm"
include "unipr.mm"
include "ex-un.mm"
include "eqtri.mm"

theorem ex-uni



  assert |- U. { { 1 , 3 } , { 1 , 8 } } = { 1 , 3 , 8 }

  proof
    c1
    c3
    cpr
    #
    c1
    c8
    cpr
    #
    cpr
    cuni
    @0
    @1
    cun
    c1
    c3
    c8
    ctp
    @0
    @1
    c1
    c3
    prex
    c1
    c8
    prex
    unipr
    ex-un
    eqtri
end
