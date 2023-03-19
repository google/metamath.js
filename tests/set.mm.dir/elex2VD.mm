include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "idn1.mm"
include "idn2.mm"
include "eleq1a.mm"
include "e12.mm"
include "in2.mm"
include "gen11.mm"
include "elisset.mm"
include "e1a.mm"
include "exim.mm"
include "e11.mm"
include "in1.mm"

theorem elex2VD
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
    cB
    wcel
    #
    vx
    wex
    #
    @0
    @1
    cA
    wceq
    #
    @2
    wi
    #
    vx
    wal
    @4
    vx
    wex
    #
    @3
    @0
    @5
    vx
    @0
    @4
    @2
    @0
    @0
    @4
    @4
    @2
    @0
    idn1
    #
    @0
    @4
    idn2
    cA
    cB
    @1
    eleq1a
    e12
    in2
    gen11
    @0
    @0
    @6
    @7
    vx
    cA
    cB
    elisset
    e1a
    @4
    @2
    vx
    exim
    e11
    in1
end
