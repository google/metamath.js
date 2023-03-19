include "cn0.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cwwlks.mm"
include "crab.mm"
include "wa.mm"
include "wwlksn.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem iswwlksn
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w


  assert |- ( N e. NN0 -> ( W e. ( N WWalksN G ) <-> ( W e. ( WWalks ` G ) /\ ( # ` W ) = ( N + 1 ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    cG
    cwwlksn
    co
    #
    wcel
    cW
    vw
    cv
    #
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    vw
    cG
    cwwlks
    cfv
    #
    crab
    #
    wcel
    cW
    @6
    wcel
    cW
    chash
    cfv
    #
    @4
    wceq
    #
    wa
    @0
    @1
    @7
    cW
    vw
    cG
    cN
    wwlksn
    eleq2d
    @5
    @9
    vw
    cW
    @6
    @2
    cW
    wceq
    @3
    @8
    @4
    @2
    cW
    chash
    fveq2
    eqeq1d
    elrab
    syl6bb
end
