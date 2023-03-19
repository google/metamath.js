include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cnei.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "eltopss.mm"
include "adantr.mm"
include "ssid.mm"
include "wceq.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "ad2ant2l.mm"
include "wb.mm"
include "isnei.mm"
include "ad2ant2r.mm"
include "mpbir2and.mm"
include "exp43.mm"
include "3imp.mm"
include "ssnei.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "impbid.mm"

theorem opnneissb
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


  assert |- ( ( J e. Top /\ N e. J /\ S C_ X ) -> ( S C_ N <-> N e. ( ( nei ` J ) ` S ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cJ
    wcel
    #
    cS
    cX
    wss
    #
    w3a
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
    @0
    @1
    @2
    @3
    @4
    wi
    @0
    @1
    @2
    @3
    @4
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    wa
    @4
    cN
    cX
    wss
    #
    cS
    vg
    cv
    #
    wss
    #
    @8
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    @5
    @7
    @6
    cN
    cJ
    cX
    neips.1
    eltopss
    adantr
    @1
    @3
    @12
    @0
    @2
    @1
    @3
    cN
    cN
    wss
    #
    @12
    cN
    ssid
    @11
    @3
    @13
    wa
    vg
    cN
    cJ
    @8
    cN
    wceq
    @9
    @3
    @10
    @13
    @8
    cN
    cS
    sseq2
    @8
    cN
    cN
    sseq1
    anbi12d
    rspcev
    mpanr2
    ad2ant2l
    @0
    @2
    @4
    @7
    @12
    wa
    wb
    @1
    @3
    cS
    vg
    cJ
    cN
    cX
    neips.1
    isnei
    ad2ant2r
    mpbir2and
    exp43
    3imp
    @0
    @1
    @4
    @3
    wi
    @2
    @0
    @4
    @3
    cS
    cJ
    cN
    ssnei
    ex
    3ad2ant1
    impbid
end
