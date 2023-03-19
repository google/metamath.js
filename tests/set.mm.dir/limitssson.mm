include "climits.mm"
include "con0.mm"
include "cbigcup.mm"
include "cfix.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-limits.mm"
include "difss.mm"
include "inss1.mm"
include "sstri.mm"
include "eqsstri.mm"

theorem limitssson



  assert |- Limits C_ On

  proof
    climits
    con0
    cbigcup
    cfix
    #
    cin
    #
    c0
    csn
    #
    cdif
    #
    con0
    df-limits
    @3
    @1
    con0
    @1
    @2
    difss
    con0
    @0
    inss1
    sstri
    eqsstri
end
