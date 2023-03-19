include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "weq.mm"
include "wrex.mm"
include "dfss3.mm"
include "clel5.mm"
include "ralbii.mm"
include "bitri.mm"

theorem dfss5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  disjoint B y
  disjoint x y
  assert |- ( A C_ B <-> A. x e. A E. y e. B x = y )

  proof
    cA
    cB
    wss
    vx
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    vx
    vy
    weq
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    vx
    cA
    cB
    dfss3
    @1
    @2
    vx
    cA
    vy
    cB
    @0
    clel5
    ralbii
    bitri
end
