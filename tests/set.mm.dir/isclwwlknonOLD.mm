include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "clwwlknonOLD.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isclwwlknonOLD
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  assume isclwwlknon.v: |- V = ( Vtx ` G )


  assert |- ( ( X e. V /\ N e. NN0 ) -> ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( W e. ( N ClWWalksN G ) /\ ( W ` 0 ) = X ) ) )

  proof
    cX
    cV
    wcel
    cN
    cn0
    wcel
    wa
    #
    cW
    cX
    cN
    cG
    cclwwlknon
    cfv
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
    wcel
    cW
    @5
    wcel
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    wa
    @0
    @1
    @6
    cW
    vw
    cG
    cN
    cV
    cX
    isclwwlknon.v
    clwwlknonOLD
    eleq2d
    @4
    @8
    vw
    cW
    @5
    @2
    cW
    wceq
    @3
    @7
    cX
    cc0
    @2
    cW
    fveq1
    eqeq1d
    elrab
    syl6bb
end
