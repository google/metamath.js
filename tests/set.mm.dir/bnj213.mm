include "cv.mm"
include "wbr.mm"
include "c-bnj14.mm"
include "df-bnj14.mm"
include "ssrab3.mm"

theorem bnj213
  let cA: class A
  let cR: class R
  let cX: class X
  let vy: setvar y


  assert |- _pred ( X , A , R ) C_ A

  proof
    vy
    cv
    cX
    cR
    wbr
    vy
    cA
    cA
    cR
    cX
    c-bnj14
    vy
    cA
    cR
    cX
    df-bnj14
    ssrab3
end
