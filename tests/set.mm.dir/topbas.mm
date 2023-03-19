include "ctop.mm"
include "wcel.mm"
include "ctb.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "inopn.mm"
include "3expb.mm"
include "simpr.mm"
include "ssid.mm"
include "jctir.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2an2r.mm"
include "exp31.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "isbasis2g.mm"
include "mpbird.mm"

theorem topbas
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cV: class V
  let cC: class C


  assert |- ( J e. Top -> J e. TopBases )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ctb
    wcel
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @2
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    wa
    #
    vw
    cJ
    wrex
    #
    vz
    @6
    wral
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    @0
    @10
    vx
    vy
    cJ
    cJ
    @0
    @4
    cJ
    wcel
    #
    @5
    cJ
    wcel
    #
    wa
    #
    @9
    vz
    @6
    @0
    @13
    @1
    @6
    wcel
    #
    @9
    @0
    @13
    wa
    #
    @6
    cJ
    wcel
    #
    @14
    @14
    @6
    @6
    wss
    #
    wa
    #
    @9
    @0
    @11
    @12
    @16
    @4
    @5
    cJ
    inopn
    3expb
    @15
    @14
    wa
    @14
    @17
    @15
    @14
    simpr
    @6
    ssid
    jctir
    @8
    @18
    vw
    @6
    cJ
    @2
    @6
    wceq
    @3
    @14
    @7
    @17
    @2
    @6
    @1
    eleq2
    @2
    @6
    @6
    sseq1
    anbi12d
    rspcev
    syl2an2r
    exp31
    ralrimdv
    ralrimivv
    vx
    vy
    vz
    vw
    cJ
    ctop
    isbasis2g
    mpbird
end
