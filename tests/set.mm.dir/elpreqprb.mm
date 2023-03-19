include "wcel.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elpreqpr.mm"
include "prid1g.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "exlimdv.mm"
include "impbid2.mm"

theorem elpreqprb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint V x
  assert |- ( A e. V -> ( A e. { B , C } <-> E. x { B , C } = { A , x } ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cC
    cpr
    #
    wcel
    #
    @1
    cA
    vx
    cv
    #
    cpr
    #
    wceq
    #
    vx
    wex
    vx
    cA
    cB
    cC
    elpreqpr
    @0
    @5
    @2
    vx
    @0
    @2
    @5
    cA
    @4
    wcel
    cA
    @3
    cV
    prid1g
    @1
    @4
    cA
    eleq2
    syl5ibrcom
    exlimdv
    impbid2
end
