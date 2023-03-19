include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cssr.mm"
include "wbr.mm"
include "wss.mm"
include "crefrels.mm"
include "crefs.mm"
include "crels.mm"
include "df-refrels.mm"
include "df-refs.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "inex1g.mm"
include "elv.mm"
include "brssr.mm"
include "ax-mp.mm"
include "wceq.mm"
include "elrels6.mm"
include "biimpi.mm"
include "sseq2d.mm"
include "syl5bb.mm"
include "abeqinbi.mm"

theorem dfrefrels2
  let vr: setvar r


  assert |- RefRels = { r e. Rels | ( _I i^i ( dom r X. ran r ) ) C_ r }

  proof
    cid
    vr
    cv
    #
    cdm
    @0
    crn
    cxp
    #
    cin
    #
    @0
    @1
    cin
    #
    cssr
    wbr
    #
    @2
    @0
    wss
    #
    vr
    crefrels
    crefs
    crels
    df-refrels
    vr
    df-refs
    @4
    @2
    @3
    wss
    #
    @0
    crels
    wcel
    #
    @5
    @3
    cvv
    wcel
    #
    @4
    @6
    wb
    @8
    vr
    @0
    @1
    cvv
    inex1g
    elv
    @2
    @3
    cvv
    brssr
    ax-mp
    @7
    @3
    @0
    @2
    @7
    @3
    @0
    wceq
    #
    @7
    @9
    wb
    vr
    @0
    cvv
    elrels6
    elv
    biimpi
    sseq2d
    syl5bb
    abeqinbi
end
