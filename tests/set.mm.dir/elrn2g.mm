include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "crn.mm"
include "wceq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "exbidv.mm"
include "dfrn3.mm"
include "elab2g.mm"

theorem elrn2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A e. V -> ( A e. ran B <-> E. x <. x , A >. e. B ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cB
    wcel
    #
    vx
    wex
    @0
    cA
    cop
    #
    cB
    wcel
    #
    vx
    wex
    vy
    cA
    cB
    crn
    cV
    @1
    cA
    wceq
    #
    @3
    @5
    vx
    @6
    @2
    @4
    cB
    @1
    cA
    @0
    opeq2
    eleq1d
    exbidv
    vx
    vy
    cB
    dfrn3
    elab2g
end
