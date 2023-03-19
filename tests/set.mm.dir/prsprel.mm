include "cpr.mm"
include "cspr.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "sprel.mm"
include "wo.mm"
include "preq12bg.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "bi2anan9.mm"
include "biimpd.mm"
include "ancomsd.mm"
include "jaoi.mm"
include "com12.mm"
include "adantl.mm"
include "sylbid.mm"
include "expcom.mm"
include "com23.mm"
include "rexlimivv.mm"
include "syl.mm"
include "imp.mm"

theorem prsprel
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( { X , Y } e. ( Pairs ` V ) /\ ( X e. U /\ Y e. W ) ) -> ( X e. V /\ Y e. V ) )

  proof
    cX
    cY
    cpr
    #
    cV
    cspr
    cfv
    wcel
    #
    cX
    cU
    wcel
    cY
    cW
    wcel
    wa
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    @1
    @0
    va
    cv
    #
    vb
    cv
    #
    cpr
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    @2
    @5
    wi
    #
    cV
    @0
    va
    vb
    sprel
    @8
    @9
    va
    vb
    cV
    cV
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    wa
    #
    @2
    @8
    @5
    @2
    @12
    @8
    @5
    wi
    @2
    @12
    wa
    @8
    cX
    @6
    wceq
    #
    cY
    @7
    wceq
    #
    wa
    #
    cX
    @7
    wceq
    #
    cY
    @6
    wceq
    #
    wa
    #
    wo
    #
    @5
    cX
    cY
    @6
    @7
    cU
    cW
    cV
    cV
    preq12bg
    @12
    @19
    @5
    wi
    @2
    @19
    @12
    @5
    @15
    @12
    @5
    wi
    @18
    @15
    @12
    @5
    @13
    @10
    @3
    @14
    @11
    @4
    @10
    @3
    wb
    @6
    cX
    @6
    cX
    cV
    eleq1
    eqcoms
    @11
    @4
    wb
    @7
    cY
    @7
    cY
    cV
    eleq1
    eqcoms
    bi2anan9
    biimpd
    @18
    @11
    @10
    @5
    @18
    @11
    @10
    wa
    @5
    @16
    @11
    @3
    @17
    @10
    @4
    @11
    @3
    wb
    @7
    cX
    @7
    cX
    cV
    eleq1
    eqcoms
    @10
    @4
    wb
    @6
    cY
    @6
    cY
    cV
    eleq1
    eqcoms
    bi2anan9
    biimpd
    ancomsd
    jaoi
    com12
    adantl
    sylbid
    expcom
    com23
    rexlimivv
    syl
    imp
end
