include "weq.mm"
include "wcel-wl.mm"
include "wi.mm"
include "wal.mm"
include "ax-wl-8cl.mm"
include "equcoms.mm"
include "impbid.mm"
include "equsalvw.mm"
include "bicomi.mm"

theorem wl-clelv2-just
  let vx: setvar x
  let vu: setvar u
  let cA: class A

  disjoint u x
  disjoint A x
  disjoint A u
  assert |- ( x wl-el A <-> A. u ( u = x -> u wl-el A ) )

  proof
    vu
    vx
    weq
    #
    vu
    cA
    wcel-wl
    #
    wi
    vu
    wal
    vx
    cA
    wcel-wl
    #
    @1
    @2
    vu
    vx
    @0
    @1
    @2
    vu
    vx
    cA
    ax-wl-8cl
    @2
    @1
    wi
    vx
    vu
    vx
    vu
    cA
    ax-wl-8cl
    equcoms
    impbid
    equsalvw
    bicomi
end
