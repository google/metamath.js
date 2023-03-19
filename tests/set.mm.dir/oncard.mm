include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wex.mm"
include "id.mm"
include "fveq2.mm"
include "cardidm.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "exlimiv.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "impbii.mm"

theorem oncard
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E. x A = ( card ` x ) <-> A = ( card ` A ) )

  proof
    cA
    vx
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    vx
    wex
    #
    cA
    cA
    ccrd
    cfv
    #
    wceq
    #
    @2
    @5
    vx
    @2
    cA
    @1
    @4
    @2
    id
    @2
    @4
    @1
    ccrd
    cfv
    @1
    cA
    @1
    ccrd
    fveq2
    @0
    cardidm
    syl6eq
    eqtr4d
    exlimiv
    cA
    cvv
    wcel
    #
    @5
    @3
    @5
    @6
    @4
    cvv
    wcel
    cA
    ccrd
    fvex
    cA
    @4
    cvv
    eleq1
    mpbiri
    @2
    @5
    vx
    cA
    cvv
    @0
    cA
    wceq
    @1
    @4
    cA
    @0
    cA
    ccrd
    fveq2
    eqeq2d
    spcegv
    mpcom
    impbii
end
