include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "cwwlksn.mm"
include "crab.mm"
include "eqid.mm"
include "iswwlksnon.mm"
include "wwlksnfi.mm"
include "rabfi.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem wwlksnonfi
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let vw: setvar w


  assert |- ( ( Vtx ` G ) e. Fin -> ( A ( N WWalksNOn G ) B ) e. Fin )

  proof
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    cc0
    vw
    cv
    #
    cfv
    cA
    wceq
    cN
    @2
    cfv
    cB
    wceq
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
    cfn
    vw
    cA
    cB
    cG
    cN
    @0
    @0
    eqid
    iswwlksnon
    @1
    @4
    cfn
    wcel
    @5
    cfn
    wcel
    cG
    cN
    wwlksnfi
    @3
    vw
    @4
    rabfi
    syl
    syl5eqel
end
