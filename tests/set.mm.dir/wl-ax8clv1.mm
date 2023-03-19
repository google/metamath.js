include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wcel-wl.mm"
include "wi.mm"
include "equvinv.mm"
include "ax-wl-8cl.mm"
include "equcoms.mm"
include "sylan9.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem wl-ax8clv1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vu: setvar u

  disjoint A x
  disjoint A y
  disjoint u x
  disjoint A u
  disjoint u y
  assert |- ( x = y -> ( x wl-el A -> y wl-el A ) )

  proof
    vx
    vy
    weq
    vu
    vx
    weq
    #
    vu
    vy
    weq
    #
    wa
    #
    vu
    wex
    vx
    cA
    wcel-wl
    #
    vy
    cA
    wcel-wl
    #
    wi
    #
    vx
    vy
    vu
    equvinv
    @2
    @5
    vu
    @0
    @3
    vu
    cA
    wcel-wl
    #
    @1
    @4
    @3
    @6
    wi
    vx
    vu
    vx
    vu
    cA
    ax-wl-8cl
    equcoms
    vu
    vy
    cA
    ax-wl-8cl
    sylan9
    exlimiv
    sylbi
end
