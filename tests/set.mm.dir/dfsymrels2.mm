include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "ccnv.mm"
include "cssr.mm"
include "wbr.mm"
include "wss.mm"
include "csymrels.mm"
include "csyms.mm"
include "crels.mm"
include "df-symrels.mm"
include "df-syms.mm"
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
include "cnveqd.mm"
include "sseq12d.mm"
include "syl5bb.mm"
include "abeqinbi.mm"

theorem dfsymrels2
  let vr: setvar r


  assert |- SymRels = { r e. Rels | `' r C_ r }

  proof
    vr
    cv
    #
    @0
    cdm
    @0
    crn
    cxp
    #
    cin
    #
    ccnv
    #
    @2
    cssr
    wbr
    #
    @0
    ccnv
    #
    @0
    wss
    #
    vr
    csymrels
    csyms
    crels
    df-symrels
    vr
    df-syms
    @4
    @3
    @2
    wss
    #
    @0
    crels
    wcel
    #
    @6
    @2
    cvv
    wcel
    #
    @4
    @7
    wb
    @9
    vr
    @0
    @1
    cvv
    inex1g
    elv
    @3
    @2
    cvv
    brssr
    ax-mp
    @8
    @3
    @5
    @2
    @0
    @8
    @2
    @0
    @8
    @2
    @0
    wceq
    #
    @8
    @10
    wb
    vr
    @0
    cvv
    elrels6
    elv
    biimpi
    #
    cnveqd
    @11
    sseq12d
    syl5bb
    abeqinbi
end
