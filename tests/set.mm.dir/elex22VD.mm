include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "wi.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "elisset.mm"
include "wal.mm"
include "idn2.mm"
include "eleq1a.mm"
include "e12.mm"
include "simpr.mm"
include "pm3.2.mm"
include "e22.mm"
include "in2.mm"
include "gen11.mm"
include "exim.mm"
include "pm2.27.mm"
include "e11.mm"
include "in1.mm"

theorem elex22VD
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
    cB
    wcel
    #
    @3
    cC
    wcel
    #
    wa
    #
    vx
    wex
    #
    @2
    @3
    cA
    wceq
    #
    vx
    wex
    #
    @9
    @7
    wi
    #
    @7
    @2
    @0
    @9
    @2
    @2
    @0
    @2
    idn1
    #
    @0
    @1
    simpl
    e1a
    #
    vx
    cA
    cB
    elisset
    e1a
    @2
    @8
    @6
    wi
    #
    vx
    wal
    @10
    @2
    @13
    vx
    @2
    @8
    @6
    @2
    @8
    @4
    @5
    @6
    @2
    @0
    @8
    @8
    @4
    @12
    @2
    @8
    idn2
    #
    cA
    cB
    @3
    eleq1a
    e12
    @2
    @1
    @8
    @8
    @5
    @2
    @2
    @1
    @11
    @0
    @1
    simpr
    e1a
    @14
    cA
    cC
    @3
    eleq1a
    e12
    @4
    @5
    pm3.2
    e22
    in2
    gen11
    @8
    @6
    vx
    exim
    e1a
    @9
    @7
    pm2.27
    e11
    in1
end
