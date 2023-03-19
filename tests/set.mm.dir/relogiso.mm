include "crp.mm"
include "cr.mm"
include "clt.mm"
include "clog.mm"
include "cres.mm"
include "wiso.mm"
include "ce.mm"
include "ccnv.mm"
include "reefiso.mm"
include "isocnv.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "dfrelog.mm"
include "isoeq1.mm"
include "mpbir.mm"

theorem relogiso



  assert |- ( log |` RR+ ) Isom < , < ( RR+ , RR )

  proof
    crp
    cr
    clt
    clt
    clog
    crp
    cres
    #
    wiso
    #
    crp
    cr
    clt
    clt
    ce
    cr
    cres
    #
    ccnv
    #
    wiso
    #
    cr
    crp
    clt
    clt
    @2
    wiso
    @4
    reefiso
    cr
    crp
    clt
    clt
    @2
    isocnv
    ax-mp
    @0
    @3
    wceq
    @1
    @4
    wb
    dfrelog
    crp
    cr
    clt
    clt
    @3
    @0
    isoeq1
    ax-mp
    mpbir
end
