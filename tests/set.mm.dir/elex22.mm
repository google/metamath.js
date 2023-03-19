include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "eleq1a.mm"
include "anim12ii.mm"
include "alrimiv.mm"
include "elisset.mm"
include "adantr.mm"
include "exim.mm"
include "sylc.mm"

theorem elex22
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A e. B /\ A e. C ) -> E. x ( x e. B /\ x e. C ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    wceq
    #
    @3
    cB
    wcel
    #
    @3
    cC
    wcel
    #
    wa
    #
    wi
    #
    vx
    wal
    @4
    vx
    wex
    #
    @7
    vx
    wex
    @2
    @8
    vx
    @0
    @4
    @5
    @1
    @6
    cA
    cB
    @3
    eleq1a
    cA
    cC
    @3
    eleq1a
    anim12ii
    alrimiv
    @0
    @9
    @1
    vx
    cA
    cB
    elisset
    adantr
    @4
    @7
    vx
    exim
    sylc
end
