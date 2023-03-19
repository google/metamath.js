include "c1.mm"
include "cc0.mm"
include "wceq.mm"
include "c1r.mm"
include "c0r.mm"
include "cop.mm"
include "1ne0sr.mm"
include "cnr.mm"
include "1sr.mm"
include "elexi.mm"
include "eqresr.mm"
include "mtbir.mm"
include "df-1.mm"
include "df-0.mm"
include "eqeq12i.mm"
include "neir.mm"

theorem ax1ne0



  assert |- 1 =/= 0

  proof
    c1
    cc0
    c1
    cc0
    wceq
    c1r
    c0r
    cop
    #
    c0r
    c0r
    cop
    #
    wceq
    #
    @2
    c1r
    c0r
    wceq
    1ne0sr
    c1r
    c0r
    c1r
    cnr
    1sr
    elexi
    eqresr
    mtbir
    c1
    @0
    cc0
    @1
    df-1
    df-0
    eqeq12i
    mtbir
    neir
end
