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
include "elab2.mm"

theorem elrn2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume elrn.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. ran B <-> E. x <. x , A >. e. B )

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
    elrn.1
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
    elab2
end
