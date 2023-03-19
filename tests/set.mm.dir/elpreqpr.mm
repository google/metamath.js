include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cvv.mm"
include "cv.mm"
include "wex.mm"
include "elpri.mm"
include "elex.mm"
include "wi.mm"
include "elpreqprlem.mm"
include "eleq1.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "imp.mm"
include "prcom.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "sylib.mm"
include "jaoian.mm"
include "syl2anc.mm"

theorem elpreqpr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A e. { B , C } -> E. x { B , C } = { A , x } )

  proof
    cA
    cB
    cC
    cpr
    #
    wcel
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    cA
    cvv
    wcel
    #
    @0
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
    #
    cA
    cB
    cC
    elpri
    cA
    @0
    elex
    @1
    @3
    @7
    @2
    @1
    @3
    @7
    @1
    @3
    @7
    wi
    #
    cB
    cvv
    wcel
    #
    @0
    cB
    @4
    cpr
    #
    wceq
    #
    vx
    wex
    #
    wi
    vx
    cB
    cC
    cvv
    elpreqprlem
    @1
    @3
    @9
    @7
    @12
    cA
    cB
    cvv
    eleq1
    @1
    @6
    @11
    vx
    @1
    @5
    @10
    @0
    cA
    cB
    @4
    preq1
    eqeq2d
    exbidv
    imbi12d
    mpbiri
    imp
    @2
    @3
    @7
    @2
    @8
    cC
    cvv
    wcel
    #
    @0
    cC
    @4
    cpr
    #
    wceq
    #
    vx
    wex
    #
    wi
    @13
    cC
    cB
    cpr
    #
    @14
    wceq
    #
    vx
    wex
    @16
    vx
    cC
    cB
    cvv
    elpreqprlem
    @18
    @15
    vx
    @17
    @0
    @14
    cC
    cB
    prcom
    eqeq1i
    exbii
    sylib
    @2
    @3
    @13
    @7
    @16
    cA
    cC
    cvv
    eleq1
    @2
    @6
    @15
    vx
    @2
    @5
    @14
    @0
    cA
    cC
    @4
    preq1
    eqeq2d
    exbidv
    imbi12d
    mpbiri
    imp
    jaoian
    syl2anc
end
