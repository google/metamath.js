include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "cfil.mm"
include "wrex.mm"
include "w3a.mm"
include "csn.mm"
include "cnei.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "eqid.mm"
include "flimclslem.mm"
include "3anass.mm"
include "sylib.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl.mm"
include "3expia.mm"
include "flimclsi.mm"
include "sselda.mm"
include "rexlimivw.mm"
include "impbid1.mm"

theorem flimcls
  let cA: class A
  let cS: class S
  let vf: setvar f
  let cJ: class J
  let cX: class X

  disjoint A f
  disjoint J f
  disjoint S f
  disjoint X f
  assert |- ( ( J e. ( TopOn ` X ) /\ S C_ X ) -> ( A e. ( ( cls ` J ) ` S ) <-> E. f e. ( Fil ` X ) ( S e. f /\ A e. ( J fLim f ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cA
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cS
    vf
    cv
    #
    wcel
    #
    cA
    cJ
    @4
    cflim
    co
    #
    wcel
    #
    wa
    #
    vf
    cX
    cfil
    cfv
    #
    wrex
    #
    @0
    @1
    @3
    @10
    @0
    @1
    @3
    w3a
    #
    cX
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    cS
    csn
    cun
    cfi
    cfv
    cfg
    co
    #
    @9
    wcel
    #
    cS
    @12
    wcel
    #
    cA
    cJ
    @12
    cflim
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    @10
    @11
    @13
    @14
    @16
    w3a
    @18
    cA
    cS
    @12
    cJ
    cX
    @12
    eqid
    flimclslem
    @13
    @14
    @16
    3anass
    sylib
    @8
    @17
    vf
    @12
    @9
    @4
    @12
    wceq
    #
    @5
    @14
    @7
    @16
    @4
    @12
    cS
    eleq2
    @19
    @6
    @15
    cA
    @4
    @12
    cJ
    cflim
    oveq2
    eleq2d
    anbi12d
    rspcev
    syl
    3expia
    @8
    @3
    vf
    @9
    @5
    @6
    @2
    cA
    cS
    @4
    cJ
    flimclsi
    sselda
    rexlimivw
    impbid1
end
