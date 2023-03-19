include "cvv.mm"
include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "elfvex.mm"
include "cpw.mm"
include "crab.mm"
include "sprvalpw.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem sprel
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let cW: class W
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint a b
  disjoint X a
  disjoint X b
  disjoint V p
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint X p
  disjoint k x
  assert |- ( X e. ( Pairs ` V ) -> E. a e. V E. b e. V X = { a , b } )

  proof
    cV
    cvv
    wcel
    #
    cX
    cV
    cspr
    cfv
    #
    wcel
    #
    cX
    va
    cv
    vb
    cv
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    cX
    cV
    cspr
    elfvex
    @0
    @2
    cX
    vp
    cv
    #
    @3
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cV
    cpw
    #
    crab
    #
    wcel
    #
    @5
    @0
    @1
    @10
    cX
    cV
    cvv
    vp
    va
    vb
    sprvalpw
    eleq2d
    @11
    cX
    @9
    wcel
    @5
    @8
    @5
    vp
    cX
    @9
    @6
    cX
    wceq
    @7
    @4
    va
    vb
    cV
    cV
    @6
    cX
    @3
    eqeq1
    2rexbidv
    elrab
    simprbi
    syl6bi
    mpcom
end
