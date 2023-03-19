include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "simplr.mm"
include "wceq.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "ssid.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "rspcev.mm"
include "adantlr.mm"
include "jca.mm"
include "ex.mm"
include "3adant1.mm"
include "wb.mm"
include "eltopss.mm"
include "isnei.mm"
include "syldan.mm"
include "3adant3.mm"
include "sylibrd.mm"
include "ssnei.mm"
include "3ad2ant1.mm"
include "impbid.mm"

theorem opnssneib
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vp: setvar p
  let vv: setvar v
  let cM: class M
  let cP: class P
  assume neips.1: |- X = U. J


  assert |- ( ( J e. Top /\ S e. J /\ N C_ X ) -> ( S C_ N <-> N e. ( ( nei ` J ) ` S ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cJ
    wcel
    #
    cN
    cX
    wss
    #
    w3a
    #
    cS
    cN
    wss
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    @3
    @4
    @2
    cS
    vg
    cv
    #
    wss
    #
    @6
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    @5
    @1
    @2
    @4
    @11
    wi
    @0
    @1
    @2
    wa
    #
    @4
    @11
    @12
    @4
    wa
    @2
    @10
    @1
    @2
    @4
    simplr
    @1
    @4
    @10
    @2
    @9
    @4
    vg
    cS
    cJ
    @6
    cS
    wceq
    #
    @9
    cS
    cS
    wss
    #
    @4
    wa
    @4
    @13
    @7
    @14
    @8
    @4
    @6
    cS
    cS
    sseq2
    @6
    cS
    cN
    sseq1
    anbi12d
    @14
    @4
    cS
    ssid
    biantrur
    syl6bbr
    rspcev
    adantlr
    jca
    ex
    3adant1
    @0
    @1
    @5
    @11
    wb
    #
    @2
    @0
    @1
    cS
    cX
    wss
    @15
    cS
    cJ
    cX
    neips.1
    eltopss
    cS
    vg
    cJ
    cN
    cX
    neips.1
    isnei
    syldan
    3adant3
    sylibrd
    @0
    @1
    @5
    @4
    wi
    @2
    @0
    @5
    @4
    cS
    cJ
    cN
    ssnei
    ex
    3ad2ant1
    impbid
end
