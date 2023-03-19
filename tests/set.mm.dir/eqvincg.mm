include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "elisset.mm"
include "ax-1.mm"
include "eqtr.mm"
include "ex.mm"
include "jca.mm"
include "eximi.mm"
include "pm3.43.mm"
include "3syl.mm"
include "19.37v.mm"
include "sylib.mm"
include "eqtr2.mm"
include "exlimiv.mm"
include "impbid1.mm"

theorem eqvincg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( A = B <-> E. x ( x = A /\ x = B ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wa
    #
    vx
    wex
    #
    @0
    @1
    @5
    wi
    #
    vx
    wex
    #
    @1
    @6
    wi
    @0
    @3
    vx
    wex
    @1
    @3
    wi
    #
    @1
    @4
    wi
    #
    wa
    #
    vx
    wex
    @8
    vx
    cA
    cV
    elisset
    @3
    @11
    vx
    @3
    @9
    @10
    @3
    @1
    ax-1
    @3
    @1
    @4
    @2
    cA
    cB
    eqtr
    ex
    jca
    eximi
    @11
    @7
    vx
    @1
    @3
    @4
    pm3.43
    eximi
    3syl
    @1
    @5
    vx
    19.37v
    sylib
    @5
    @1
    vx
    @2
    cA
    cB
    eqtr2
    exlimiv
    impbid1
end
