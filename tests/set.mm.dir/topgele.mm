include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "wss.mm"
include "cpw.mm"
include "ctop.mm"
include "topontop.mm"
include "0opn.mm"
include "syl.mm"
include "toponmax.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "0ex.mm"
include "prssg.mm"
include "sylancr.mm"
include "mpbi2and.mm"
include "cuni.mm"
include "wceq.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "jca.mm"

theorem topgele
  let cJ: class J
  let cX: class X


  assert |- ( J e. ( TopOn ` X ) -> ( { (/) , X } C_ J /\ J C_ ~P X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    c0
    cX
    cpr
    cJ
    wss
    #
    cJ
    cX
    cpw
    wss
    #
    @0
    c0
    cJ
    wcel
    #
    cX
    cJ
    wcel
    #
    @1
    @0
    cJ
    ctop
    wcel
    @3
    cX
    cJ
    topontop
    cJ
    0opn
    syl
    cX
    cJ
    toponmax
    #
    @0
    c0
    cvv
    wcel
    @4
    @3
    @4
    wa
    @1
    wb
    0ex
    @5
    c0
    cX
    cJ
    cvv
    cJ
    prssg
    sylancr
    mpbi2and
    @0
    cJ
    cuni
    #
    cX
    wss
    #
    @2
    @0
    cX
    @6
    wceq
    @7
    cX
    cJ
    toponuni
    @6
    cX
    eqimss2
    syl
    cJ
    cX
    sspwuni
    sylibr
    jca
end
