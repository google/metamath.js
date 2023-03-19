include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cale.mm"
include "crn.mm"
include "cen.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "con0.mm"
include "cardidm.mm"
include "wss.mm"
include "wb.mm"
include "cardom.mm"
include "simpr.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "simpl.mm"
include "carddom2.mm"
include "sylancr.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "cardalephex.mm"
include "syl.mm"
include "mpbii.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylib.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fvelrnb.mm"
include "sylibr.mm"
include "cardid2.mm"
include "adantr.mm"
include "breq1.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem infenaleph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. dom card /\ _om ~<_ A ) -> E. x e. ran aleph x ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cale
    crn
    #
    wcel
    #
    @4
    cA
    cen
    wbr
    #
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vx
    @5
    wrex
    @3
    @8
    cale
    cfv
    #
    @4
    wceq
    #
    vx
    con0
    wrex
    #
    @6
    @3
    @4
    @10
    wceq
    #
    vx
    con0
    wrex
    #
    @12
    @3
    @4
    ccrd
    cfv
    @4
    wceq
    #
    @14
    cA
    cardidm
    @3
    com
    @4
    wss
    @15
    @14
    wb
    @3
    com
    com
    ccrd
    cfv
    #
    @4
    cardom
    @3
    @16
    @4
    wss
    #
    @2
    @1
    @2
    simpr
    @3
    com
    @0
    wcel
    #
    @1
    @17
    @2
    wb
    com
    con0
    wcel
    @18
    omelon
    com
    onenon
    ax-mp
    @1
    @2
    simpl
    com
    cA
    carddom2
    sylancr
    mpbird
    syl5eqssr
    vx
    @4
    cardalephex
    syl
    mpbii
    @13
    @11
    vx
    con0
    @4
    @10
    eqcom
    rexbii
    sylib
    cale
    con0
    wfn
    @6
    @12
    wb
    alephfnon
    vx
    con0
    @4
    cale
    fvelrnb
    ax-mp
    sylibr
    @1
    @7
    @2
    cA
    cardid2
    adantr
    @9
    @7
    vx
    @4
    @5
    @8
    @4
    cA
    cen
    breq1
    rspcev
    syl2anc
end
