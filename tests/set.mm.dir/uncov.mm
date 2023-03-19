include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cv.mm"
include "cunc.mm"
include "wbr.mm"
include "cio.mm"
include "cfv.mm"
include "co.mm"
include "coprab.mm"
include "df-br.mm"
include "df-unc.mm"
include "eleq2i.mm"
include "bitri.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "wceq.mm"
include "weq.mm"
include "w3a.mm"
include "simp2.mm"
include "fveq2.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "breq123d.mm"
include "eloprabga.mm"
include "mp3an3.mm"
include "syl5bb.mm"
include "iotabidv.mm"
include "df-ov.mm"
include "df-fv.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem uncov
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. V /\ B e. W ) -> ( A uncurry F B ) = ( ( F ` A ) ` B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    vw
    cv
    #
    cF
    cunc
    #
    wbr
    #
    vw
    cio
    #
    cB
    @4
    cA
    cF
    cfv
    #
    wbr
    #
    vw
    cio
    cA
    cB
    @5
    co
    #
    cB
    @8
    cfv
    @2
    @6
    @9
    vw
    @6
    @3
    @4
    cop
    #
    vy
    cv
    #
    vz
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    #
    wcel
    #
    @2
    @9
    @6
    @11
    @5
    wcel
    @18
    @3
    @4
    @5
    df-br
    @5
    @17
    @11
    vx
    vy
    vz
    cF
    df-unc
    eleq2i
    bitri
    @0
    @1
    @4
    cvv
    wcel
    @18
    @9
    wb
    vw
    vex
    @16
    @9
    vx
    vy
    vz
    cA
    cB
    @4
    cV
    cW
    cvv
    @14
    cA
    wceq
    #
    @12
    cB
    wceq
    #
    vz
    vw
    weq
    #
    w3a
    @12
    cB
    @13
    @4
    @15
    @8
    @19
    @20
    @21
    simp2
    @19
    @20
    @15
    @8
    wceq
    @21
    @14
    cA
    cF
    fveq2
    3ad2ant1
    @19
    @20
    @21
    simp3
    breq123d
    eloprabga
    mp3an3
    syl5bb
    iotabidv
    @10
    @3
    @5
    cfv
    @7
    cA
    cB
    @5
    df-ov
    vw
    @3
    @5
    df-fv
    eqtri
    vw
    cB
    @8
    df-fv
    3eqtr4g
end
