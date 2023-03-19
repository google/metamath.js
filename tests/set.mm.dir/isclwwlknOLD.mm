include "cn.mm"
include "wcel.mm"
include "cclwwlknold.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "crab.mm"
include "wa.mm"
include "clwwlknOLD.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isclwwlknOLD
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w


  assert |- ( N e. NN -> ( W e. ( N ClWWalksNOLD G ) <-> ( W e. ( ClWWalks ` G ) /\ ( # ` W ) = N ) ) )

  proof
    cN
    cn
    wcel
    #
    cW
    cN
    cG
    cclwwlknold
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
    wceq
    #
    vw
    cG
    cclwwlk
    cfv
    #
    crab
    #
    wcel
    cW
    @5
    wcel
    cW
    chash
    cfv
    #
    cN
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
    clwwlknOLD
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
    cN
    @2
    cW
    chash
    fveq2
    eqeq1d
    elrab
    syl6bb
end
