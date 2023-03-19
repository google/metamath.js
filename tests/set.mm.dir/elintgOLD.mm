include "cv.mm"
include "cint.mm"
include "wcel.mm"
include "wral.mm"
include "eleq1.mm"
include "wceq.mm"
include "ralbidv.mm"
include "vex.mm"
include "elint2.mm"
include "vtoclbg.mm"

theorem elintgOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. V -> ( A e. |^| B <-> A. x e. B A e. x ) )

  proof
    vy
    cv
    #
    cB
    cint
    #
    wcel
    @0
    vx
    cv
    #
    wcel
    #
    vx
    cB
    wral
    cA
    @1
    wcel
    cA
    @2
    wcel
    #
    vx
    cB
    wral
    vy
    cA
    cV
    @0
    cA
    @1
    eleq1
    @0
    cA
    wceq
    @3
    @4
    vx
    cB
    @0
    cA
    @2
    eleq1
    ralbidv
    vx
    @0
    cB
    vy
    vex
    elint2
    vtoclbg
end
