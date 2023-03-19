include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "c-bnj14.mm"
include "breq2.mm"
include "rabbidv.mm"
include "df-bnj14.mm"
include "3eqtr4g.mm"

theorem bnj602
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vy: setvar y


  assert |- ( X = Y -> _pred ( X , A , R ) = _pred ( Y , A , R ) )

  proof
    cX
    cY
    wceq
    #
    vy
    cv
    #
    cX
    cR
    wbr
    #
    vy
    cA
    crab
    @1
    cY
    cR
    wbr
    #
    vy
    cA
    crab
    cA
    cR
    cX
    c-bnj14
    cA
    cR
    cY
    c-bnj14
    @0
    @2
    @3
    vy
    cA
    cX
    cY
    @1
    cR
    breq2
    rabbidv
    vy
    cA
    cR
    cX
    df-bnj14
    vy
    cA
    cR
    cY
    df-bnj14
    3eqtr4g
end
