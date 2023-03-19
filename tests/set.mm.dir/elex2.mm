include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "eleq1a.mm"
include "alrimiv.mm"
include "elisset.mm"
include "exim.mm"
include "sylc.mm"

theorem elex2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. B -> E. x x e. B )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    @1
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @2
    vx
    wex
    @3
    vx
    wex
    @0
    @4
    vx
    cA
    cB
    @1
    eleq1a
    alrimiv
    vx
    cA
    cB
    elisset
    @2
    @3
    vx
    exim
    sylc
end
