include "cnpi.mm"
include "clti.mm"
include "wor.mm"
include "cep.mm"
include "con0.mm"
include "wss.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-ni.mm"
include "difss.mm"
include "omsson.mm"
include "sstri.mm"
include "eqsstri.mm"
include "wwe.mm"
include "epweon.mm"
include "weso.mm"
include "ax-mp.mm"
include "soss.mm"
include "mp2.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "df-lti.mm"
include "soeq1.mm"
include "soinxp.mm"
include "bitr4i.mm"
include "mpbir.mm"

theorem ltsopi



  assert |- <N Or N.

  proof
    cnpi
    clti
    wor
    #
    cnpi
    cep
    wor
    #
    cnpi
    con0
    wss
    con0
    cep
    wor
    #
    @1
    cnpi
    com
    c0
    csn
    #
    cdif
    #
    con0
    df-ni
    @4
    com
    con0
    com
    @3
    difss
    omsson
    sstri
    eqsstri
    con0
    cep
    wwe
    @2
    epweon
    con0
    cep
    weso
    ax-mp
    cnpi
    con0
    cep
    soss
    mp2
    @0
    cnpi
    cep
    cnpi
    cnpi
    cxp
    cin
    #
    wor
    #
    @1
    clti
    @5
    wceq
    @0
    @6
    wb
    df-lti
    cnpi
    clti
    @5
    soeq1
    ax-mp
    cnpi
    cep
    soinxp
    bitr4i
    mpbir
end
