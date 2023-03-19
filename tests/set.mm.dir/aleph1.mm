include "c1o.mm"
include "cale.mm"
include "cfv.mm"
include "c0.mm"
include "csuc.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cdom.mm"
include "df-1o.mm"
include "fveq2i.mm"
include "cpw.mm"
include "wbr.mm"
include "alephsucpw.mm"
include "cen.mm"
include "wb.mm"
include "fvex.mm"
include "pw2en.mm"
include "domen2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "eqbrtri.mm"

theorem aleph1



  assert |- ( aleph ` 1o ) ~<_ ( 2o ^m ( aleph ` (/) ) )

  proof
    c1o
    cale
    cfv
    c0
    csuc
    #
    cale
    cfv
    #
    c2o
    c0
    cale
    cfv
    #
    cmap
    co
    #
    cdom
    c1o
    @0
    cale
    df-1o
    fveq2i
    @1
    @2
    cpw
    #
    cdom
    wbr
    #
    @1
    @3
    cdom
    wbr
    #
    c0
    alephsucpw
    @4
    @3
    cen
    wbr
    @5
    @6
    wb
    @2
    c0
    cale
    fvex
    pw2en
    @4
    @3
    @1
    domen2
    ax-mp
    mpbi
    eqbrtri
end
