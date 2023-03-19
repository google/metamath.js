include "cmnf.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cltrr.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "olc.mm"
include "mp2an.mm"
include "orci.mm"
include "cxr.mm"
include "wb.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "ltxr.mm"
include "mpbir.mm"

theorem mnfltpnf



  assert |- -oo < +oo

  proof
    cmnf
    cpnf
    clt
    wbr
    #
    cmnf
    cr
    wcel
    #
    cpnf
    cr
    wcel
    #
    wa
    cmnf
    cpnf
    cltrr
    wbr
    wa
    #
    cmnf
    cmnf
    wceq
    #
    cpnf
    cpnf
    wceq
    #
    wa
    #
    wo
    #
    @1
    @5
    wa
    @4
    @2
    wa
    wo
    #
    wo
    #
    @7
    @8
    @4
    @5
    @7
    cmnf
    eqid
    cpnf
    eqid
    @6
    @3
    olc
    mp2an
    orci
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    @0
    @9
    wb
    mnfxr
    pnfxr
    cmnf
    cpnf
    ltxr
    mp2an
    mpbir
end
