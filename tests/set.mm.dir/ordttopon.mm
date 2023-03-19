include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "csn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cuni.mm"
include "ctopon.mm"
include "ctg.mm"
include "eqid.mm"
include "ordtval.mm"
include "ctb.mm"
include "fibas.mm"
include "tgtopon.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "ordtuni.mm"
include "cvv.mm"
include "wceq.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "fiuni.mm"
include "syl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"

theorem ordttopon
  let cR: class R
  let cV: class V
  let cX: class X
  let cA: class A
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let cP: class P
  assume ordttopon.3: |- X = dom R


  assert |- ( R e. V -> ( ordTop ` R ) e. ( TopOn ` X ) )

  proof
    cR
    cV
    wcel
    #
    cR
    cordt
    cfv
    #
    cX
    csn
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    wn
    vy
    cX
    crab
    cmpt
    crn
    #
    vx
    cX
    @3
    @2
    cR
    wbr
    wn
    vy
    cX
    crab
    cmpt
    crn
    #
    cun
    cun
    #
    cfi
    cfv
    #
    cuni
    #
    ctopon
    cfv
    #
    cX
    ctopon
    cfv
    @0
    @1
    @7
    ctg
    cfv
    #
    @9
    vx
    vy
    @4
    @5
    cR
    cV
    cX
    ordttopon.3
    @4
    eqid
    #
    @5
    eqid
    #
    ordtval
    @7
    ctb
    wcel
    @10
    @9
    wcel
    @6
    fibas
    @7
    tgtopon
    ax-mp
    syl6eqel
    @0
    cX
    @8
    ctopon
    @0
    cX
    @6
    cuni
    #
    @8
    vx
    vy
    @4
    @5
    cR
    cV
    cX
    ordttopon.3
    @11
    @12
    ordtuni
    #
    @0
    @6
    cvv
    wcel
    #
    @13
    @8
    wceq
    @0
    @13
    cvv
    wcel
    @15
    @0
    cX
    @13
    cvv
    @14
    @0
    cX
    cR
    cdm
    cvv
    ordttopon.3
    cR
    cV
    dmexg
    syl5eqel
    eqeltrrd
    @6
    uniexb
    sylibr
    @6
    cvv
    fiuni
    syl
    eqtrd
    fveq2d
    eleqtrrd
end
