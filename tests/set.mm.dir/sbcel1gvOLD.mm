include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "eleq1.mm"
include "clelsb3.mm"
include "vtoclbg.mm"

theorem sbcel1gvOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A e. V -> ( [. A / x ]. x e. B <-> A e. B ) )

  proof
    vx
    cv
    cB
    wcel
    #
    vx
    vy
    wsb
    vy
    cv
    #
    cB
    wcel
    @0
    vx
    cA
    wsbc
    cA
    cB
    wcel
    vy
    cA
    cV
    @0
    vx
    vy
    cA
    dfsbcq2
    @1
    cA
    cB
    eleq1
    vy
    vx
    cB
    clelsb3
    vtoclbg
end
