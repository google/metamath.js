include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "wrdnval.mm"
include "eleq2d.mm"
include "syl5bbr.mm"

theorem wrdmap
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w


  assert |- ( ( V e. X /\ N e. NN0 ) -> ( ( W e. Word V /\ ( # ` W ) = N ) <-> W e. ( V ^m ( 0 ..^ N ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    cW
    vw
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    vw
    @0
    crab
    #
    wcel
    cV
    cX
    wcel
    cN
    cn0
    wcel
    wa
    #
    cW
    cV
    cc0
    cN
    cfzo
    co
    cmap
    co
    #
    wcel
    @5
    @2
    vw
    cW
    @0
    @3
    cW
    wceq
    @4
    @1
    cN
    @3
    cW
    chash
    fveq2
    eqeq1d
    elrab
    @7
    @6
    @8
    cW
    vw
    cN
    cV
    cX
    wrdnval
    eleq2d
    syl5bbr
end
