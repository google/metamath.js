include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "csn.mm"
include "eleq1.mm"
include "pm5.32ri.mm"
include "baib.mm"
include "abbidv.mm"
include "df-rab.mm"
include "df-sn.mm"
include "3eqtr4g.mm"

theorem rabsn
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( B e. A -> { x e. A | x = B } = { B } )

  proof
    cB
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cB
    wceq
    #
    wa
    #
    vx
    cab
    @3
    vx
    cab
    @3
    vx
    cA
    crab
    cB
    csn
    @0
    @4
    @3
    vx
    @4
    @0
    @3
    @3
    @2
    @0
    @1
    cB
    cA
    eleq1
    pm5.32ri
    baib
    abbidv
    @3
    vx
    cA
    df-rab
    vx
    cB
    df-sn
    3eqtr4g
end
