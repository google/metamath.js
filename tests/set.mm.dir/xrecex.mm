include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cxmu.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "cmul.mm"
include "ax-rrecex.mm"
include "wb.mm"
include "wi.mm"
include "rexmul.mm"
include "eqeq1d.mm"
include "ex.mm"
include "adantr.mm"
include "pm5.32d.mm"
include "rexbidv2.mm"
include "mpbird.mm"

theorem xrecex
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A *e x ) = 1 )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    vx
    cv
    #
    cxmu
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    cA
    @3
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    vx
    cA
    ax-rrecex
    @2
    @5
    @7
    vx
    cr
    cr
    @2
    @3
    cr
    wcel
    #
    @5
    @7
    @0
    @8
    @5
    @7
    wb
    #
    wi
    @1
    @0
    @8
    @9
    @0
    @8
    wa
    @4
    @6
    c1
    cA
    @3
    rexmul
    eqeq1d
    ex
    adantr
    pm5.32d
    rexbidv2
    mpbird
end
