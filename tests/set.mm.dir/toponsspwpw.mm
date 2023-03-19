include "cvv.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "ctop.mm"
include "crab.mm"
include "cab.mm"
include "rabssab.mm"
include "eqcom.mm"
include "abbii.mm"
include "sseqtri.mm"
include "pwpwssunieq.mm"
include "sstri.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "eqeq1.mm"
include "rabbidv.mm"
include "df-topon.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "syl6eqss.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem toponsspwpw
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( TopOn ` A ) C_ ~P ~P A

  proof
    cA
    cvv
    wcel
    #
    cA
    ctopon
    cfv
    #
    cA
    cpw
    #
    cpw
    #
    wss
    @0
    @1
    cA
    vy
    cv
    cuni
    #
    wceq
    #
    vy
    ctop
    crab
    #
    @3
    @0
    @6
    cvv
    wcel
    #
    @1
    @6
    wceq
    @0
    @6
    @3
    wss
    @3
    cvv
    wcel
    #
    @7
    @6
    @4
    cA
    wceq
    #
    vy
    cab
    #
    @3
    @6
    @5
    vy
    cab
    @10
    @5
    vy
    ctop
    rabssab
    @5
    @9
    vy
    cA
    @4
    eqcom
    abbii
    sseqtri
    vy
    cA
    pwpwssunieq
    sstri
    #
    @0
    @2
    cvv
    wcel
    @8
    cA
    cvv
    pwexg
    @2
    cvv
    pwexg
    syl
    @6
    @3
    cvv
    ssexg
    sylancr
    vx
    cA
    vx
    cv
    #
    @4
    wceq
    #
    vy
    ctop
    crab
    @6
    cvv
    cvv
    ctopon
    @12
    cA
    wceq
    @13
    @5
    vy
    ctop
    @12
    cA
    @4
    eqeq1
    rabbidv
    vy
    vx
    df-topon
    fvmptg
    mpdan
    @11
    syl6eqss
    @0
    wn
    @1
    c0
    @3
    cA
    ctopon
    fvprc
    @3
    0ss
    syl6eqss
    pm2.61i
end
