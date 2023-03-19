include "c2.mm"
include "clgs.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "wcel.mm"
include "cneg.mm"
include "cif.mm"
include "cz.mm"
include "wceq.mm"
include "2z.mm"
include "lgs2.mm"
include "ax-mp.mm"
include "iddvds.mm"
include "iftruei.mm"
include "eqtri.mm"

theorem 2lgs2



  assert |- ( 2 /L 2 ) = 0

  proof
    c2
    c2
    clgs
    co
    #
    c2
    c2
    cdvds
    wbr
    #
    cc0
    c2
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    c1
    c1
    cneg
    cif
    #
    cif
    #
    cc0
    c2
    cz
    wcel
    #
    @0
    @3
    wceq
    2z
    c2
    lgs2
    ax-mp
    @1
    cc0
    @2
    @4
    @1
    2z
    c2
    iddvds
    ax-mp
    iftruei
    eqtri
end
