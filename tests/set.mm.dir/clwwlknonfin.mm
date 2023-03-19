include "cfn.mm"
include "wcel.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "clwwlknon.mm"
include "cvtx.mm"
include "eleq1i.mm"
include "clwwlknfi.mm"
include "sylbi.mm"
include "rabfi.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem clwwlknonfin
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vw: setvar w
  assume clwwlknonfin.v: |- V = ( Vtx ` G )


  assert |- ( V e. Fin -> ( X ( ClWWalksNOn ` G ) N ) e. Fin )

  proof
    cV
    cfn
    wcel
    #
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    cc0
    vw
    cv
    cfv
    cX
    wceq
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    cfn
    vw
    cG
    cN
    cX
    clwwlknon
    @0
    @2
    cfn
    wcel
    #
    @3
    cfn
    wcel
    @0
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    @4
    cV
    @5
    cfn
    clwwlknonfin.v
    eleq1i
    cG
    cN
    clwwlknfi
    sylbi
    @1
    vw
    @2
    rabfi
    syl
    syl5eqel
end
