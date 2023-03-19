include "wcel.mm"
include "cid.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cres.mm"
include "cvv.mm"
include "cop.mm"
include "ccusgr.mm"
include "wex.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "cusgrexilem1.mm"
include "cusgrexi.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "spcegv.mm"
include "sylc.mm"

theorem cusgrexg
  let ve: setvar e
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y

  disjoint V e
  disjoint V x
  disjoint V y
  disjoint x y
  disjoint e y
  disjoint W x
  assert |- ( V e. W -> E. e <. V , e >. e. ComplUSGraph )

  proof
    cV
    cW
    wcel
    cid
    vy
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vy
    cV
    cpw
    #
    crab
    #
    cres
    #
    cvv
    wcel
    cV
    @5
    cop
    #
    ccusgr
    wcel
    #
    cV
    ve
    cv
    #
    cop
    #
    ccusgr
    wcel
    #
    ve
    wex
    vx
    @4
    cV
    cW
    @2
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    vy
    vx
    @3
    vy
    vx
    weq
    @1
    @12
    c2
    @0
    @11
    chash
    fveq2
    eqeq1d
    cbvrabv
    #
    cusgrexilem1
    vx
    @4
    cV
    cW
    @13
    cusgrexi
    @10
    @7
    ve
    @5
    cvv
    @8
    @5
    wceq
    @9
    @6
    ccusgr
    @8
    @5
    cV
    opeq2
    eleq1d
    spcegv
    sylc
end
