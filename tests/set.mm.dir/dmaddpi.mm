include "coa.mm"
include "cnpi.mm"
include "cxp.mm"
include "cres.mm"
include "cdm.mm"
include "con0.mm"
include "cin.mm"
include "cpli.mm"
include "dmres.mm"
include "wfn.mm"
include "wceq.mm"
include "fnoa.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "df-pli.mm"
include "dmeqi.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-ni.mm"
include "difss.mm"
include "eqsstri.mm"
include "omsson.mm"
include "sstri.mm"
include "anidm.mm"
include "mpbir.mm"
include "xpss12.mm"
include "dfss.mm"
include "mpbi.mm"
include "3eqtr4i.mm"

theorem dmaddpi



  assert |- dom +N = ( N. X. N. )

  proof
    coa
    cnpi
    cnpi
    cxp
    #
    cres
    #
    cdm
    #
    @0
    con0
    con0
    cxp
    #
    cin
    #
    cpli
    cdm
    @0
    @2
    @0
    coa
    cdm
    #
    cin
    @4
    coa
    @0
    dmres
    @5
    @3
    @0
    coa
    @3
    wfn
    @5
    @3
    wceq
    fnoa
    @3
    coa
    fndm
    ax-mp
    ineq2i
    eqtri
    cpli
    @1
    df-pli
    dmeqi
    @0
    @3
    wss
    #
    @0
    @4
    wceq
    cnpi
    con0
    wss
    #
    @7
    wa
    #
    @6
    @8
    @7
    cnpi
    com
    con0
    cnpi
    com
    c0
    csn
    #
    cdif
    com
    df-ni
    com
    @9
    difss
    eqsstri
    omsson
    sstri
    @7
    anidm
    mpbir
    cnpi
    con0
    cnpi
    con0
    xpss12
    ax-mp
    @0
    @3
    dfss
    mpbi
    3eqtr4i
end
