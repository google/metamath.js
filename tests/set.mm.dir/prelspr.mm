include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cpw.mm"
include "crab.mm"
include "cspr.mm"
include "cfv.mm"
include "prelpwi.mm"
include "eqidd.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "preq2.mm"
include "rspc2ev.mm"
include "mpd3an3.mm"
include "jca.mm"
include "adantl.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "sprvalpw.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem prelspr
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( V e. W /\ ( X e. V /\ Y e. V ) ) -> { X , Y } e. ( Pairs ` V ) )

  proof
    cV
    cW
    wcel
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
    wa
    #
    cX
    cY
    cpr
    #
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cV
    cpw
    #
    crab
    #
    cV
    cspr
    cfv
    #
    @4
    @5
    @12
    wcel
    #
    @5
    @9
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    wa
    #
    @5
    @13
    wcel
    @3
    @18
    @0
    @3
    @15
    @17
    cX
    cY
    cV
    prelpwi
    @1
    @2
    @5
    @5
    wceq
    #
    @17
    @3
    @5
    eqidd
    @16
    @19
    @5
    cX
    @8
    cpr
    #
    wceq
    va
    vb
    cX
    cY
    cV
    cV
    @7
    cX
    wceq
    @9
    @20
    @5
    @7
    cX
    @8
    preq1
    eqeq2d
    @8
    cY
    wceq
    @20
    @5
    @5
    @8
    cY
    cX
    preq2
    eqeq2d
    rspc2ev
    mpd3an3
    jca
    adantl
    @11
    @17
    vp
    @5
    @12
    @6
    @5
    wceq
    @10
    @16
    va
    vb
    cV
    cV
    @6
    @5
    @9
    eqeq1
    2rexbidv
    elrab
    sylibr
    @0
    @14
    @13
    wceq
    @3
    cV
    cW
    vp
    va
    vb
    sprvalpw
    adantr
    eleqtrrd
end
