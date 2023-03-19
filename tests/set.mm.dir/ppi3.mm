include "c3.mm"
include "cppi.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "2nn0.mm"
include "df-3.mm"
include "ppi2.mm"
include "3prm.mm"
include "ppi1i.mm"
include "df-2.mm"
include "eqtr4i.mm"

theorem ppi3



  assert |- ( ppi ` 3 ) = 2

  proof
    c3
    cppi
    cfv
    c1
    c1
    caddc
    co
    c2
    c1
    c2
    c3
    2nn0
    df-3
    ppi2
    3prm
    ppi1i
    df-2
    eqtr4i
end
