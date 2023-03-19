include "cale.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "com.mm"
include "wss.mm"
include "ccrd.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "alephfnon.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "alephgeom.mm"
include "biimpi.mm"
include "sseq2.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "pm4.71ri.mm"
include "eqcom.mm"
include "rexbii.mm"
include "cardalephex.mm"
include "pm5.32i.mm"
include "3bitr4i.mm"
include "bitr2i.mm"

theorem isinfcard
  let cA: class A
  let vx: setvar x


  assert |- ( ( _om C_ A /\ ( card ` A ) = A ) <-> A e. ran aleph )

  proof
    cA
    cale
    crn
    wcel
    #
    vx
    cv
    #
    cale
    cfv
    #
    cA
    wceq
    #
    vx
    con0
    wrex
    #
    com
    cA
    wss
    #
    cA
    ccrd
    cfv
    cA
    wceq
    #
    wa
    #
    cale
    con0
    wfn
    @0
    @4
    wb
    alephfnon
    vx
    con0
    cA
    cale
    fvelrnb
    ax-mp
    cA
    @2
    wceq
    #
    vx
    con0
    wrex
    #
    @5
    @9
    wa
    @4
    @7
    @9
    @5
    @8
    @5
    vx
    con0
    @1
    con0
    wcel
    #
    @5
    @8
    com
    @2
    wss
    #
    @10
    @11
    @1
    alephgeom
    biimpi
    cA
    @2
    com
    sseq2
    syl5ibrcom
    rexlimiv
    pm4.71ri
    @3
    @8
    vx
    con0
    @2
    cA
    eqcom
    rexbii
    @5
    @6
    @9
    vx
    cA
    cardalephex
    pm5.32i
    3bitr4i
    bitr2i
end
