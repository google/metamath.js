include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccmp.mm"
include "wss.mm"
include "w3a.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "topontop.mm"
include "3ad2ant1.mm"
include "elpwi.mm"
include "wa.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl3.mm"
include "sstrd.mm"
include "simpl1.mm"
include "toponuni.mm"
include "syl.mm"
include "simprr.mm"
include "eqtrd.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "iscmp.mm"
include "sylanbrc.mm"

theorem sscmp
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume sscmp.1: |- X = U. K


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. Comp /\ J C_ K ) -> J e. Comp )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    ccmp
    wcel
    #
    cJ
    cK
    wss
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    vx
    cv
    #
    cuni
    #
    wceq
    #
    @5
    vy
    cv
    cuni
    #
    wceq
    #
    vy
    @6
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vx
    cJ
    cpw
    #
    wral
    cJ
    ccmp
    wcel
    @0
    @1
    @4
    @2
    cX
    cJ
    topontop
    3ad2ant1
    @3
    @13
    vx
    @14
    @6
    @14
    wcel
    @3
    @6
    cJ
    wss
    #
    @13
    @6
    cJ
    elpwi
    @3
    @15
    @8
    @12
    @3
    @15
    @8
    wa
    #
    wa
    #
    cX
    @9
    wceq
    #
    vy
    @11
    wrex
    #
    @12
    @17
    @1
    @6
    cK
    wss
    cX
    @7
    wceq
    @19
    @0
    @1
    @2
    @16
    simpl2
    @17
    @6
    cJ
    cK
    @3
    @15
    @8
    simprl
    @0
    @1
    @2
    @16
    simpl3
    sstrd
    @17
    cX
    @5
    @7
    @17
    @0
    cX
    @5
    wceq
    @0
    @1
    @2
    @16
    simpl1
    cX
    cJ
    toponuni
    syl
    #
    @3
    @15
    @8
    simprr
    eqtrd
    @6
    cK
    cX
    vy
    sscmp.1
    cmpcov
    syl3anc
    @17
    @18
    @10
    vy
    @11
    @17
    cX
    @5
    @9
    @20
    eqeq1d
    rexbidv
    mpbid
    expr
    sylan2
    ralrimiva
    vx
    vy
    cJ
    @5
    @5
    eqid
    iscmp
    sylanbrc
end
