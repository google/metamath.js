include "wel.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "cint.mm"
include "wceq.mm"
include "eleq1.mm"
include "ralbidv.mm"
include "dfint2.mm"
include "elab2g.mm"

theorem elintg
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
    vx
    wel
    #
    vx
    cB
    wral
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cB
    wral
    vy
    cA
    cB
    cint
    cV
    vy
    cv
    #
    cA
    wceq
    @0
    @2
    vx
    cB
    @3
    cA
    @1
    eleq1
    ralbidv
    vy
    vx
    cB
    dfint2
    elab2g
end
