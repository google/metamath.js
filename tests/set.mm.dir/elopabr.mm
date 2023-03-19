include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "df-br.mm"
include "biimpi.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "imp.mm"
include "exlimivv.mm"
include "sylbi.mm"

theorem elopabr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( A e. { <. x , y >. | x R y } -> A e. R )

  proof
    cA
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
    wcel
    cA
    @0
    @1
    cop
    #
    wceq
    #
    @2
    wa
    #
    vy
    wex
    vx
    wex
    cA
    cR
    wcel
    #
    @2
    vx
    vy
    cA
    elopab
    @5
    @6
    vx
    vy
    @4
    @2
    @6
    @2
    @6
    @4
    @3
    cR
    wcel
    #
    @2
    @7
    @0
    @1
    cR
    df-br
    biimpi
    cA
    @3
    cR
    eleq1
    syl5ibr
    imp
    exlimivv
    sylbi
end
