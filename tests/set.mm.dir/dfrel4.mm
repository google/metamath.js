include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wceq.mm"
include "dfrel4v.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq12.mm"
include "cbvopab.mm"
include "eqeq2i.mm"
include "bitri.mm"

theorem dfrel4
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let va: setvar a
  let vb: setvar b
  assume dfrel4.1: |- F/_ x R
  assume dfrel4.2: |- F/_ y R

  disjoint x y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint R a
  disjoint R b
  assert |- ( Rel R <-> R = { <. x , y >. | x R y } )

  proof
    cR
    wrel
    cR
    va
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    va
    vb
    copab
    #
    wceq
    cR
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    copab
    #
    wceq
    va
    vb
    cR
    dfrel4v
    @3
    @7
    cR
    @2
    @6
    va
    vb
    vx
    vy
    vx
    @0
    @1
    cR
    vx
    @0
    nfcv
    dfrel4.1
    vx
    @1
    nfcv
    nfbr
    vy
    @0
    @1
    cR
    vy
    @0
    nfcv
    dfrel4.2
    vy
    @1
    nfcv
    nfbr
    @6
    va
    nfv
    @6
    vb
    nfv
    @0
    @4
    @1
    @5
    cR
    breq12
    cbvopab
    eqeq2i
    bitri
end
