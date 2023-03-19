include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "eleq2.mm"
include "ceqsexgv.mm"
include "bicomd.mm"

theorem clel3g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( B e. V -> ( A e. B <-> E. x ( x = B /\ A e. x ) ) )

  proof
    cB
    cV
    wcel
    vx
    cv
    #
    cB
    wceq
    cA
    @0
    wcel
    #
    wa
    vx
    wex
    cA
    cB
    wcel
    #
    @1
    @2
    vx
    cB
    cV
    @0
    cB
    cA
    eleq2
    ceqsexgv
    bicomd
end
