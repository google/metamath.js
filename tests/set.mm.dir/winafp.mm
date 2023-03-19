include "cwina.mm"
include "wcel.mm"
include "com.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "wceq.mm"
include "wlim.mm"
include "winalim2.mm"
include "wss.mm"
include "con0.mm"
include "cvv.mm"
include "vex.mm"
include "limelon.mm"
include "mpan.mm"
include "alephle.mm"
include "syl.mm"
include "ad2antll.mm"
include "simprl.mm"
include "sseqtrd.mm"
include "ccf.mm"
include "fveq2d.mm"
include "alephsing.mm"
include "eqtr3d.mm"
include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "elwina.mm"
include "simp2bi.mm"
include "ad2antrr.mm"
include "cfle.mm"
include "syl6eqssr.mm"
include "eqssd.mm"
include "exlimddv.mm"

theorem winafp
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. InaccW /\ A =/= _om ) -> ( aleph ` A ) = A )

  proof
    cA
    cwina
    wcel
    #
    cA
    com
    wne
    #
    wa
    #
    vx
    cv
    #
    cale
    cfv
    #
    cA
    wceq
    #
    @3
    wlim
    #
    wa
    #
    cA
    cale
    cfv
    #
    cA
    wceq
    vx
    vx
    cA
    winalim2
    @2
    @7
    wa
    #
    @4
    @8
    cA
    @9
    @3
    cA
    cale
    @9
    @3
    cA
    @9
    @3
    @4
    cA
    @6
    @3
    @4
    wss
    #
    @2
    @5
    @6
    @3
    con0
    wcel
    #
    @10
    @3
    cvv
    wcel
    @6
    @11
    vx
    vex
    @3
    cvv
    limelon
    mpan
    @3
    alephle
    syl
    ad2antll
    @2
    @5
    @6
    simprl
    #
    sseqtrd
    @9
    cA
    @3
    ccf
    cfv
    #
    @3
    @9
    cA
    ccf
    cfv
    #
    @13
    cA
    @9
    @4
    ccf
    cfv
    #
    @14
    @13
    @9
    @4
    cA
    ccf
    @12
    fveq2d
    @6
    @15
    @13
    wceq
    @2
    @5
    @3
    alephsing
    ad2antll
    eqtr3d
    @0
    @14
    cA
    wceq
    #
    @1
    @7
    @0
    cA
    c0
    wne
    @16
    vy
    cv
    vz
    cv
    csdm
    wbr
    vz
    cA
    wrex
    vy
    cA
    wral
    vy
    vz
    cA
    elwina
    simp2bi
    ad2antrr
    eqtr3d
    @3
    cfle
    syl6eqssr
    eqssd
    fveq2d
    @12
    eqtr3d
    exlimddv
end
