include "cv.mm"
include "wbr.mm"
include "c-bnj14.mm"
include "breq1.mm"
include "df-bnj14.mm"
include "elrab2.mm"

theorem bnj1152
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vy: setvar y


  assert |- ( Y e. _pred ( X , A , R ) <-> ( Y e. A /\ Y R X ) )

  proof
    vy
    cv
    #
    cX
    cR
    wbr
    cY
    cX
    cR
    wbr
    vy
    cY
    cA
    cA
    cR
    cX
    c-bnj14
    @0
    cY
    cX
    cR
    breq1
    vy
    cA
    cR
    cX
    df-bnj14
    elrab2
end
