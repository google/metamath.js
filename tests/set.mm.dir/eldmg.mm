include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cdm.mm"
include "wceq.mm"
include "breq1.mm"
include "exbidv.mm"
include "df-dm.mm"
include "elab2g.mm"

theorem eldmg
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( A e. dom B <-> E. y A B y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cB
    wbr
    #
    vy
    wex
    cA
    @1
    cB
    wbr
    #
    vy
    wex
    vx
    cA
    cB
    cdm
    cV
    @0
    cA
    wceq
    @2
    @3
    vy
    @0
    cA
    @1
    cB
    breq1
    exbidv
    vx
    vy
    cB
    df-dm
    elab2g
end
