include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cipo.mm"
include "cfv.mm"
include "cdrs.mm"
include "pwexg.mm"
include "inex1g.mm"
include "syl.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "ne0i.mm"
include "mp1i.mm"
include "wa.mm"
include "elpwi.mm"
include "anim12i.mm"
include "unss.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "bitr4i.mm"
include "sylib.mm"
include "ad2ant2r.mm"
include "unfi.mm"
include "ad2ant2l.mm"
include "elind.mm"
include "syl2anb.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylancl.mm"
include "rgen2a.mm"
include "a1i.mm"
include "isipodrs.mm"
include "syl3anbrc.mm"

theorem fpwipodrs
  let cA: class A
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( A e. V -> ( toInc ` ( ~P A i^i Fin ) ) e. Dirset )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    cfn
    cin
    #
    cvv
    wcel
    #
    @2
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    vz
    cv
    #
    wss
    #
    vz
    @2
    wrex
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @2
    cipo
    cfv
    cdrs
    wcel
    @0
    @1
    cvv
    wcel
    @3
    cA
    cV
    pwexg
    @1
    cfn
    cvv
    inex1g
    syl
    c0
    @2
    wcel
    #
    @4
    @0
    @12
    c0
    @1
    wcel
    c0
    cfn
    wcel
    cA
    0elpw
    0fin
    c0
    @1
    cfn
    elin
    mpbir2an
    @2
    c0
    ne0i
    mp1i
    @11
    @0
    @10
    vx
    vy
    @2
    @5
    @2
    wcel
    #
    @6
    @2
    wcel
    #
    wa
    @7
    @2
    wcel
    #
    @7
    @7
    wss
    #
    @10
    @13
    @5
    @1
    wcel
    #
    @5
    cfn
    wcel
    #
    wa
    #
    @6
    @1
    wcel
    #
    @6
    cfn
    wcel
    #
    wa
    #
    @15
    @14
    @5
    @1
    cfn
    elin
    @6
    @1
    cfn
    elin
    @19
    @22
    wa
    @1
    cfn
    @7
    @17
    @20
    @7
    @1
    wcel
    #
    @18
    @21
    @17
    @20
    wa
    @5
    cA
    wss
    #
    @6
    cA
    wss
    #
    wa
    #
    @23
    @17
    @24
    @20
    @25
    @5
    cA
    elpwi
    @6
    cA
    elpwi
    anim12i
    @26
    @7
    cA
    wss
    @23
    @5
    @6
    cA
    unss
    @7
    cA
    @5
    @6
    vx
    vex
    vy
    vex
    unex
    elpw
    bitr4i
    sylib
    ad2ant2r
    @18
    @21
    @7
    cfn
    wcel
    @17
    @20
    @5
    @6
    unfi
    ad2ant2l
    elind
    syl2anb
    @7
    ssid
    @9
    @16
    vz
    @7
    @2
    @8
    @7
    @7
    sseq2
    rspcev
    sylancl
    rgen2a
    a1i
    vx
    vy
    vz
    @2
    isipodrs
    syl3anbrc
end
