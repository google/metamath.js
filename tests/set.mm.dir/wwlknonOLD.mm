include "wcel.mm"
include "wa.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "crab.mm"
include "w3a.mm"
include "iswwlksnonOLD.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem wwlknonOLD
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vf: setvar f
  assume wwlknon.v: |- V = ( Vtx ` G )


  assert |- ( ( A e. V /\ B e. V ) -> ( W e. ( A ( N WWalksNOn G ) B ) <-> ( W e. ( N WWalksN G ) /\ ( W ` 0 ) = A /\ ( W ` N ) = B ) ) )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cW
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    #
    wcel
    cW
    cc0
    vw
    cv
    #
    cfv
    #
    cA
    wceq
    #
    cN
    @2
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    wcel
    #
    cW
    @8
    wcel
    #
    cc0
    cW
    cfv
    #
    cA
    wceq
    #
    cN
    cW
    cfv
    #
    cB
    wceq
    #
    w3a
    #
    @0
    @1
    @9
    cW
    vw
    cA
    cB
    cG
    cN
    cV
    wwlknon.v
    iswwlksnonOLD
    eleq2d
    @10
    @11
    @13
    @15
    wa
    #
    wa
    @16
    @7
    @17
    vw
    cW
    @8
    @2
    cW
    wceq
    #
    @4
    @13
    @6
    @15
    @18
    @3
    @12
    cA
    cc0
    @2
    cW
    fveq1
    eqeq1d
    @18
    @5
    @14
    cB
    cN
    @2
    cW
    fveq1
    eqeq1d
    anbi12d
    elrab
    @11
    @13
    @15
    3anass
    bitr4i
    syl6bb
end
